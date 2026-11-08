import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0407Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0407Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition0407Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input0) = fromList transition0407Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0407Raw1 : List ℕ := [128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0407Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input1) = fromList transition0407Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0407Raw2 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition0407Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input2) = fromList transition0407Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input3 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0407Raw3 : List ℕ := [128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0407Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input3) = fromList transition0407Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input4 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition0407Raw4 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition0407Chunk4 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input4) = fromList transition0407Raw4 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input5 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0407Raw5 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0407Chunk5 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input5) = fromList transition0407Raw5 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input6 : List ℕ := [768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition0407Raw6 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition0407Chunk6 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input6) = fromList transition0407Raw6 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0407Input7 : List ℕ := [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition0407Raw7 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0407Chunk7 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0407Input7) = fromList transition0407Raw7 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0407 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0051 = 2 • support0643 := by
  have hs : support0051 = fromList transition0407Input0 + fromList transition0407Input1 + fromList transition0407Input2 + fromList transition0407Input3 + fromList transition0407Input4 + fromList transition0407Input5 + fromList transition0407Input6 + fromList transition0407Input7 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0407Chunk0, transition0407Chunk1, transition0407Chunk2, transition0407Chunk3, transition0407Chunk4, transition0407Chunk5, transition0407Chunk6, transition0407Chunk7]
  have hn : (transition0407Raw0 : Multiset ℕ) + (transition0407Raw1 : Multiset ℕ) + (transition0407Raw2 : Multiset ℕ) + (transition0407Raw3 : Multiset ℕ) + (transition0407Raw4 : Multiset ℕ) + (transition0407Raw5 : Multiset ℕ) + (transition0407Raw6 : Multiset ℕ) + (transition0407Raw7 : Multiset ℕ) = 2 • (supportNumbers0643 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0643] using hm

private def transition0408Input0 : List ℕ := [0, 2, 640, 642]
private def transition0408Raw0 : List ℕ := [0, 2, 384, 386]
private theorem transition0408Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0408Input0) = fromList transition0408Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0408 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0052 = 1 • support0098 := by
  have hs : support0052 = fromList transition0408Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0408Chunk0]
  have hn : (transition0408Raw0 : Multiset ℕ) = 1 • (supportNumbers0098 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0098] using hm

private def transition0409Input0 : List ℕ := [0, 2, 640, 642]
private def transition0409Raw0 : List ℕ := [0, 640, 2, 642, 384, 768, 386, 770]
private theorem transition0409Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0409Input0) = fromList transition0409Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0409 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0052 = 1 • support0099 := by
  have hs : support0052 = fromList transition0409Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0409Chunk0]
  have hn : (transition0409Raw0 : Multiset ℕ) = 1 • (supportNumbers0099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0099] using hm

private def transition0410Input0 : List ℕ := [0, 2, 640, 642]
private def transition0410Raw0 : List ℕ := [0, 2, 384, 386]
private theorem transition0410Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0410Input0) = fromList transition0410Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0410 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0052 = 1 • support0098 := by
  have hs : support0052 = fromList transition0410Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0410Chunk0]
  have hn : (transition0410Raw0 : Multiset ℕ) = 1 • (supportNumbers0098 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0098] using hm

private def transition0411Input0 : List ℕ := [0, 2, 384, 386]
private def transition0411Raw0 : List ℕ := [0, 130]
private theorem transition0411Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0411Input0) = fromList transition0411Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0411 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0098 = 1 • support0795 := by
  have hs : support0098 = fromList transition0411Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0411Chunk0]
  have hn : (transition0411Raw0 : Multiset ℕ) = 1 • (supportNumbers0795 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0795] using hm

private def transition0412Input0 : List ℕ := [0, 2, 384, 386]
private def transition0412Raw0 : List ℕ := [0, 578, 704, 130]
private theorem transition0412Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0412Input0) = fromList transition0412Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0412 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0098 = 1 • support0796 := by
  have hs : support0098 = fromList transition0412Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0412Chunk0]
  have hn : (transition0412Raw0 : Multiset ℕ) = 1 • (supportNumbers0796 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0796] using hm

private def transition0413Input0 : List ℕ := [0, 2, 640, 642]
private def transition0413Raw0 : List ℕ := [0, 544, 2, 546, 384, 928, 386, 930]
private theorem transition0413Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0413Input0) = fromList transition0413Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0413 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0052 = 1 • support0798 := by
  have hs : support0052 = fromList transition0413Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0413Chunk0]
  have hn : (transition0413Raw0 : Multiset ℕ) = 1 • (supportNumbers0798 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0798] using hm

private def transition0414Input0 : List ℕ := [0, 2, 384, 386, 544, 546, 928, 930]
private def transition0414Raw0 : List ℕ := [0, 2, 128, 130, 288, 290, 416, 418]
private theorem transition0414Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0414Input0) = fromList transition0414Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0414 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0798 = 1 • support0799 := by
  have hs : support0798 = fromList transition0414Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0414Chunk0]
  have hn : (transition0414Raw0 : Multiset ℕ) = 1 • (supportNumbers0799 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0799] using hm

private def transition0415Input0 : List ℕ := [0, 2, 384, 386, 544, 546, 928, 930]
private def transition0415Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 288, 864, 290, 866, 416, 992, 418, 994]
private theorem transition0415Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0415Input0) = fromList transition0415Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0415 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0798 = 1 • support0800 := by
  have hs : support0798 = fromList transition0415Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0415Chunk0]
  have hn : (transition0415Raw0 : Multiset ℕ) = 1 • (supportNumbers0800 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0800] using hm

private def transition0416Input0 : List ℕ := [0, 2, 136, 138]
private def transition0416Raw0 : List ℕ := [0, 2]
private theorem transition0416Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0416Input0) = fromList transition0416Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0416 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0053 = 1 • support0008 := by
  have hs : support0053 = fromList transition0416Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0416Chunk0]
  have hn : (transition0416Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0417Input0 : List ℕ := [0, 2, 136, 138]
private def transition0417Raw0 : List ℕ := [0, 2, 520, 522]
private theorem transition0417Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0417Input0) = fromList transition0417Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0417 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0053 = 1 • support0100 := by
  have hs : support0053 = fromList transition0417Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0417Chunk0]
  have hn : (transition0417Raw0 : Multiset ℕ) = 1 • (supportNumbers0100 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0100] using hm

private def transition0418Input0 : List ℕ := [0, 2, 136, 138]
private def transition0418Raw0 : List ℕ := [0, 2]
private theorem transition0418Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0418Input0) = fromList transition0418Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0418 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0053 = 1 • support0008 := by
  have hs : support0053 = fromList transition0418Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0418Chunk0]
  have hn : (transition0418Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0419Input0 : List ℕ := [0, 2, 136, 138]
private def transition0419Raw0 : List ℕ := [0, 2, 680, 682]
private theorem transition0419Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0419Input0) = fromList transition0419Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0419 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0053 = 1 • support0802 := by
  have hs : support0053 = fromList transition0419Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0419Chunk0]
  have hn : (transition0419Raw0 : Multiset ℕ) = 1 • (supportNumbers0802 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0802] using hm

private def transition0420Input0 : List ℕ := [0, 2, 680, 682]
private def transition0420Raw0 : List ℕ := [0, 2, 424, 426]
private theorem transition0420Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0420Input0) = fromList transition0420Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0420 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0802 = 1 • support0803 := by
  have hs : support0802 = fromList transition0420Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0420Chunk0]
  have hn : (transition0420Raw0 : Multiset ℕ) = 1 • (supportNumbers0803 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0803] using hm

private def transition0421Input0 : List ℕ := [0, 2, 680, 682]
private def transition0421Raw0 : List ℕ := [0, 576, 2, 578, 424, 1000, 426, 1002]
private theorem transition0421Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0421Input0) = fromList transition0421Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0421 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0802 = 1 • support0804 := by
  have hs : support0802 = fromList transition0421Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0421Chunk0]
  have hn : (transition0421Raw0 : Multiset ℕ) = 1 • (supportNumbers0804 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0804] using hm

private def transition0422Input0 : List ℕ := [0, 2, 136, 138]
private def transition0422Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0422Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0422Input0) = fromList transition0422Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0422 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0053 = 1 • support0053 := by
  have hs : support0053 = fromList transition0422Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0422Chunk0]
  have hn : (transition0422Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0423Input0 : List ℕ := [0, 2, 136, 138]
private def transition0423Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522]
private theorem transition0423Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0423Input0) = fromList transition0423Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0423 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0053 = 1 • support0101 := by
  have hs : support0053 = fromList transition0423Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0423Chunk0]
  have hn : (transition0423Raw0 : Multiset ℕ) = 1 • (supportNumbers0101 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0101] using hm

private def transition0424Input0 : List ℕ := [0, 2, 136, 138]
private def transition0424Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0424Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0424Input0) = fromList transition0424Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0424 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0053 = 1 • support0053 := by
  have hs : support0053 = fromList transition0424Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0424Chunk0]
  have hn : (transition0424Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0425Input0 : List ℕ := [0, 2, 136, 138]
private def transition0425Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682]
private theorem transition0425Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0425Input0) = fromList transition0425Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0425 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0053 = 1 • support0806 := by
  have hs : support0053 = fromList transition0425Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0425Chunk0]
  have hn : (transition0425Raw0 : Multiset ℕ) = 1 • (supportNumbers0806 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0806] using hm

private def transition0426Input0 : List ℕ := [0, 2, 136, 138, 544, 546, 680, 682]
private def transition0426Raw0 : List ℕ := [0, 2, 136, 138, 288, 290, 424, 426]
private theorem transition0426Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0426Input0) = fromList transition0426Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0426 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0806 = 1 • support0550 := by
  have hs : support0806 = fromList transition0426Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0426Chunk0]
  have hn : (transition0426Raw0 : Multiset ℕ) = 1 • (supportNumbers0550 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0550] using hm

private def transition0427Input0 : List ℕ := [0, 2, 136, 138, 544, 546, 680, 682]
private def transition0427Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 288, 864, 290, 866, 424, 1000, 426, 1002]
private theorem transition0427Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0427Input0) = fromList transition0427Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0427 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0806 = 1 • support0551 := by
  have hs : support0806 = fromList transition0427Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0427Chunk0]
  have hn : (transition0427Raw0 : Multiset ℕ) = 1 • (supportNumbers0551 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0551] using hm

private def transition0428Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0428Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition0428Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0428Input0) = fromList transition0428Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0428 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0054 = 1 • support0000 := by
  have hs : support0054 = fromList transition0428Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0428Chunk0]
  have hn : (transition0428Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition0429Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0429Raw0 : List ℕ := [0, 2, 520, 522, 8, 10, 512, 514]
private theorem transition0429Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0429Input0) = fromList transition0429Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0429 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0054 = 1 • support0102 := by
  have hs : support0054 = fromList transition0429Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0429Chunk0]
  have hn : (transition0429Raw0 : Multiset ℕ) = 1 • (supportNumbers0102 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0102] using hm

private def transition0430Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0430Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition0430Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0430Input0) = fromList transition0430Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0430 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0054 = 1 • support0000 := by
  have hs : support0054 = fromList transition0430Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0430Chunk0]
  have hn : (transition0430Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition0431Input0 : List ℕ := [0, 2, 8, 10]
private def transition0431Raw0 : List ℕ := [0, 8]
private theorem transition0431Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0431Input0) = fromList transition0431Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0431 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0000 = 1 • support0807 := by
  have hs : support0000 = fromList transition0431Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0431Chunk0]
  have hn : (transition0431Raw0 : Multiset ℕ) = 1 • (supportNumbers0807 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0807] using hm

private def transition0432Input0 : List ℕ := [0, 2, 8, 10]
private def transition0432Raw0 : List ℕ := [0, 578, 8, 586]
private theorem transition0432Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0432Input0) = fromList transition0432Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0432 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0000 = 1 • support0808 := by
  have hs : support0000 = fromList transition0432Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0432Chunk0]
  have hn : (transition0432Raw0 : Multiset ℕ) = 1 • (supportNumbers0808 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0808] using hm

private def transition0433Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0433Raw0 : List ℕ := [0, 2, 680, 682, 8, 10, 672, 674]
private theorem transition0433Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0433Input0) = fromList transition0433Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0433 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0054 = 1 • support0810 := by
  have hs : support0054 = fromList transition0433Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0433Chunk0]
  have hn : (transition0433Raw0 : Multiset ℕ) = 1 • (supportNumbers0810 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0810] using hm

private def transition0434Input0 : List ℕ := [0, 2, 8, 10, 672, 674, 680, 682]
private def transition0434Raw0 : List ℕ := [0, 2, 8, 10, 416, 418, 424, 426]
private theorem transition0434Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0434Input0) = fromList transition0434Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0434 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0810 = 1 • support0811 := by
  have hs : support0810 = fromList transition0434Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0434Chunk0]
  have hn : (transition0434Raw0 : Multiset ℕ) = 1 • (supportNumbers0811 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0811] using hm

private def transition0435Input0 : List ℕ := [0, 2, 8, 10, 672, 674, 680, 682]
private def transition0435Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition0435Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0435Input0) = fromList transition0435Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0435 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0810 = 1 • support0812 := by
  have hs : support0810 = fromList transition0435Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0435Chunk0]
  have hn : (transition0435Raw0 : Multiset ℕ) = 1 • (supportNumbers0812 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0812] using hm

private def transition0436Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 520, 522, 640, 642, 768, 770, 904, 906]
private def transition0436Raw0 : List ℕ := [0, 2, 136, 138, 8, 10, 128, 130, 264, 266, 384, 386, 256, 258, 392, 394]
private theorem transition0436Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0436Input0) = fromList transition0436Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0436 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0055 = 1 • support0103 := by
  have hs : support0055 = fromList transition0436Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0436Chunk0]
  have hn : (transition0436Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition0437Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 520, 522, 640, 642, 768, 770, 904, 906]
private def transition0437Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 8, 648, 10, 650, 128, 512, 130, 514, 264, 904, 266, 906, 384, 768, 386, 770, 256, 896, 258, 898, 392, 776, 394, 778]
private theorem transition0437Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0437Input0) = fromList transition0437Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0437 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0055 = 1 • support0104 := by
  have hs : support0055 = fromList transition0437Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0437Chunk0]
  have hn : (transition0437Raw0 : Multiset ℕ) = 1 • (supportNumbers0104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0104] using hm

private def transition0438Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 520, 522, 640, 642, 768, 770, 904, 906]
private def transition0438Raw0 : List ℕ := [0, 2, 136, 138, 8, 10, 128, 130, 264, 266, 384, 386, 256, 258, 392, 394]
private theorem transition0438Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0438Input0) = fromList transition0438Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0438 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0055 = 1 • support0103 := by
  have hs : support0055 = fromList transition0438Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0438Chunk0]
  have hn : (transition0438Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
