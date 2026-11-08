import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1806Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition1806Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition1806Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1806Input0) = fromList transition1806Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1806Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1806Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1806Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1806Input1) = fromList transition1806Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1806Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1806Raw2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition1806Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1806Input2) = fromList transition1806Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1806Input3 : List ℕ := [776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863, 904, 905, 906, 907, 908, 909, 910, 911, 920, 921, 922, 923, 924, 925, 926, 927, 968, 969, 970, 971, 972, 973, 974, 975, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition1806Raw3 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition1806Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1806Input3) = fromList transition1806Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1806 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0249 = 1 • support0050 := by
  have hs : support0249 = fromList transition1806Input0 + fromList transition1806Input1 + fromList transition1806Input2 + fromList transition1806Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1806Chunk0, transition1806Chunk1, transition1806Chunk2, transition1806Chunk3]
  have hn : (transition1806Raw0 : Multiset ℕ) + (transition1806Raw1 : Multiset ℕ) + (transition1806Raw2 : Multiset ℕ) + (transition1806Raw3 : Multiset ℕ) = 1 • (supportNumbers0050 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0050] using hm

private def transition1807Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition1807Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition1807Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1807Input0) = fromList transition1807Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1807Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1807Raw1 : List ℕ := [8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition1807Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1807Input1) = fromList transition1807Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1807Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1807Raw2 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition1807Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1807Input2) = fromList transition1807Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1807Input3 : List ℕ := [776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863, 904, 905, 906, 907, 908, 909, 910, 911, 920, 921, 922, 923, 924, 925, 926, 927, 968, 969, 970, 971, 972, 973, 974, 975, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition1807Raw3 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition1807Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1807Input3) = fromList transition1807Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1807 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0249 = 1 • support0643 := by
  have hs : support0249 = fromList transition1807Input0 + fromList transition1807Input1 + fromList transition1807Input2 + fromList transition1807Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1807Chunk0, transition1807Chunk1, transition1807Chunk2, transition1807Chunk3]
  have hn : (transition1807Raw0 : Multiset ℕ) + (transition1807Raw1 : Multiset ℕ) + (transition1807Raw2 : Multiset ℕ) + (transition1807Raw3 : Multiset ℕ) = 1 • (supportNumbers0643 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0643] using hm

private def transition1808Input0 : List ℕ := [0, 2, 256, 258]
private def transition1808Raw0 : List ℕ := [0, 2]
private theorem transition1808Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1808Input0) = fromList transition1808Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1808 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0250 = 1 • support0008 := by
  have hs : support0250 = fromList transition1808Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1808Chunk0]
  have hn : (transition1808Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition1809Input0 : List ℕ := [0, 2, 256, 258]
private def transition1809Raw0 : List ℕ := [0, 2, 640, 642]
private theorem transition1809Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1809Input0) = fromList transition1809Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1809 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0250 = 1 • support0052 := by
  have hs : support0250 = fromList transition1809Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1809Chunk0]
  have hn : (transition1809Raw0 : Multiset ℕ) = 1 • (supportNumbers0052 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0052] using hm

private def transition1810Input0 : List ℕ := [0, 2, 256, 258]
private def transition1810Raw0 : List ℕ := [0, 2]
private theorem transition1810Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1810Input0) = fromList transition1810Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1810 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0250 = 1 • support0008 := by
  have hs : support0250 = fromList transition1810Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1810Chunk0]
  have hn : (transition1810Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition1811Input0 : List ℕ := [0, 2, 256, 258]
private def transition1811Raw0 : List ℕ := [0, 2, 544, 546]
private theorem transition1811Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1811Input0) = fromList transition1811Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1811 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0250 = 1 • support0644 := by
  have hs : support0250 = fromList transition1811Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1811Chunk0]
  have hn : (transition1811Raw0 : Multiset ℕ) = 1 • (supportNumbers0644 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0644] using hm

private def transition1812Input0 : List ℕ := [0, 2, 256, 258, 640, 642, 896, 898]
private def transition1812Raw0 : List ℕ := [0, 2, 0, 2, 384, 386, 384, 386]
private theorem transition1812Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1812Input0) = fromList transition1812Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1812 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0251 = 2 • support0098 := by
  have hs : support0251 = fromList transition1812Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1812Chunk0]
  have hn : (transition1812Raw0 : Multiset ℕ) = 2 • (supportNumbers0098 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0098] using hm

private def transition1813Input0 : List ℕ := [0, 2, 256, 258, 640, 642, 896, 898]
private def transition1813Raw0 : List ℕ := [0, 640, 2, 642, 0, 640, 2, 642, 384, 768, 386, 770, 384, 768, 386, 770]
private theorem transition1813Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1813Input0) = fromList transition1813Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1813 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0251 = 2 • support0099 := by
  have hs : support0251 = fromList transition1813Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1813Chunk0]
  have hn : (transition1813Raw0 : Multiset ℕ) = 2 • (supportNumbers0099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0099] using hm

private def transition1814Input0 : List ℕ := [0, 2, 256, 258, 640, 642, 896, 898]
private def transition1814Raw0 : List ℕ := [0, 2, 0, 2, 384, 386, 384, 386]
private theorem transition1814Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1814Input0) = fromList transition1814Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1814 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0251 = 2 • support0098 := by
  have hs : support0251 = fromList transition1814Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1814Chunk0]
  have hn : (transition1814Raw0 : Multiset ℕ) = 2 • (supportNumbers0098 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0098] using hm

private def transition1815Input0 : List ℕ := [0, 2, 256, 258, 640, 642, 896, 898]
private def transition1815Raw0 : List ℕ := [0, 544, 2, 546, 0, 544, 2, 546, 384, 928, 386, 930, 384, 928, 386, 930]
private theorem transition1815Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1815Input0) = fromList transition1815Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1815 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0251 = 2 • support0798 := by
  have hs : support0251 = fromList transition1815Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1815Chunk0]
  have hn : (transition1815Raw0 : Multiset ℕ) = 2 • (supportNumbers0798 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0798] using hm

private def transition1816Input0 : List ℕ := [0, 2, 128, 130]
private def transition1816Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1816Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1816Input0) = fromList transition1816Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1816 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0252 = 1 • support0252 := by
  have hs : support0252 = fromList transition1816Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1816Chunk0]
  have hn : (transition1816Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1817Input0 : List ℕ := [0, 2, 128, 130]
private def transition1817Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1817Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1817Input0) = fromList transition1817Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1817 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0252 = 1 • support0252 := by
  have hs : support0252 = fromList transition1817Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1817Chunk0]
  have hn : (transition1817Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1818Input0 : List ℕ := [0, 2, 128, 130]
private def transition1818Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1818Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1818Input0) = fromList transition1818Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1818 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0252 = 1 • support0252 := by
  have hs : support0252 = fromList transition1818Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1818Chunk0]
  have hn : (transition1818Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1819Input0 : List ℕ := [0, 2, 128, 130]
private def transition1819Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1819Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1819Input0) = fromList transition1819Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1819 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0252 = 1 • support0252 := by
  have hs : support0252 = fromList transition1819Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1819Chunk0]
  have hn : (transition1819Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1820Input0 : List ℕ := [0, 2, 128, 130]
private def transition1820Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1820Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1820Input0) = fromList transition1820Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1820 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0252 = 1 • support0252 := by
  have hs : support0252 = fromList transition1820Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1820Chunk0]
  have hn : (transition1820Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1821Input0 : List ℕ := [0, 2, 128, 130]
private def transition1821Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706]
private theorem transition1821Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1821Input0) = fromList transition1821Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1821 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0252 = 1 • support1022 := by
  have hs : support0252 = fromList transition1821Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1821Chunk0]
  have hn : (transition1821Raw0 : Multiset ℕ) = 1 • (supportNumbers1022 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1022] using hm

private def transition1822Input0 : List ℕ := [0, 2, 128, 130, 512, 514, 640, 642]
private def transition1822Raw0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private theorem transition1822Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1822Input0) = fromList transition1822Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1822 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0253 = 1 • support0167 := by
  have hs : support0253 = fromList transition1822Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1822Chunk0]
  have hn : (transition1822Raw0 : Multiset ℕ) = 1 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition1823Input0 : List ℕ := [0, 2, 128, 130, 512, 514, 640, 642]
private def transition1823Raw0 : List ℕ := [0, 640, 2, 642, 128, 512, 130, 514, 256, 896, 258, 898, 384, 768, 386, 770]
private theorem transition1823Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1823Input0) = fromList transition1823Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1823 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0253 = 1 • support0168 := by
  have hs : support0253 = fromList transition1823Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1823Chunk0]
  have hn : (transition1823Raw0 : Multiset ℕ) = 1 • (supportNumbers0168 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0168] using hm

private def transition1824Input0 : List ℕ := [0, 2, 128, 130, 512, 514, 640, 642]
private def transition1824Raw0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private theorem transition1824Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1824Input0) = fromList transition1824Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1824 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0253 = 1 • support0167 := by
  have hs : support0253 = fromList transition1824Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1824Chunk0]
  have hn : (transition1824Raw0 : Multiset ℕ) = 1 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition1825Input0 : List ℕ := [0, 2, 128, 130, 512, 514, 640, 642]
private def transition1825Raw0 : List ℕ := [0, 544, 2, 546, 128, 672, 130, 674, 256, 800, 258, 802, 384, 928, 386, 930]
private theorem transition1825Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1825Input0) = fromList transition1825Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1825 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0253 = 1 • support1024 := by
  have hs : support0253 = fromList transition1825Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1825Chunk0]
  have hn : (transition1825Raw0 : Multiset ℕ) = 1 • (supportNumbers1024 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1024] using hm

private def transition1826Input0 : List ℕ := [0, 2, 8, 10]
private def transition1826Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1826Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1826Input0) = fromList transition1826Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1826 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0000 = 1 • support0000 := by
  have hs : support0000 = fromList transition1826Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1826Chunk0]
  have hn : (transition1826Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1827Input0 : List ℕ := [0, 2, 8, 10]
private def transition1827Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650]
private theorem transition1827Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1827Input0) = fromList transition1827Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1827 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0000 = 1 • support0256 := by
  have hs : support0000 = fromList transition1827Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1827Chunk0]
  have hn : (transition1827Raw0 : Multiset ℕ) = 1 • (supportNumbers0256 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0256] using hm

private def transition1828Input0 : List ℕ := [0, 2, 8, 10]
private def transition1828Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1828Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1828Input0) = fromList transition1828Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1828 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0000 = 1 • support0000 := by
  have hs : support0000 = fromList transition1828Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1828Chunk0]
  have hn : (transition1828Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1829Input0 : List ℕ := [0, 2, 8, 10]
private def transition1829Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554]
private theorem transition1829Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1829Input0) = fromList transition1829Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1829 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0000 = 1 • support1273 := by
  have hs : support0000 = fromList transition1829Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1829Chunk0]
  have hn : (transition1829Raw0 : Multiset ℕ) = 1 • (supportNumbers1273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1273] using hm

private def transition1830Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1830Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition1830Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1830Input0) = fromList transition1830Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1830 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0254 = 1 • support0053 := by
  have hs : support0254 = fromList transition1830Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1830Chunk0]
  have hn : (transition1830Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition1831Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1831Raw0 : List ℕ := [0, 2, 648, 650, 512, 514, 136, 138]
private theorem transition1831Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1831Input0) = fromList transition1831Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1831 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0254 = 1 • support0344 := by
  have hs : support0254 = fromList transition1831Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1831Chunk0]
  have hn : (transition1831Raw0 : Multiset ℕ) = 1 • (supportNumbers0344 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0344] using hm

private def transition1832Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1832Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition1832Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1832Input0) = fromList transition1832Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1832 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0254 = 1 • support0053 := by
  have hs : support0254 = fromList transition1832Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1832Chunk0]
  have hn : (transition1832Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition1833Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1833Raw0 : List ℕ := [0, 2, 552, 554, 672, 674, 136, 138]
private theorem transition1833Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1833Input0) = fromList transition1833Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1833 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0254 = 1 • support1476 := by
  have hs : support0254 = fromList transition1833Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1833Chunk0]
  have hn : (transition1833Raw0 : Multiset ℕ) = 1 • (supportNumbers1476 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1476] using hm

private def transition1834Input0 : List ℕ := [0, 2, 136, 138, 552, 554, 672, 674]
private def transition1834Raw0 : List ℕ := [0, 2, 136, 138, 296, 298, 416, 418]
private theorem transition1834Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1834Input0) = fromList transition1834Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1834 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1476 = 1 • support1477 := by
  have hs : support1476 = fromList transition1834Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1834Chunk0]
  have hn : (transition1834Raw0 : Multiset ℕ) = 1 • (supportNumbers1477 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1477] using hm

private def transition1835Input0 : List ℕ := [0, 2, 136, 138, 552, 554, 672, 674]
private def transition1835Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 296, 872, 298, 874, 416, 992, 418, 994]
private theorem transition1835Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1835Input0) = fromList transition1835Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1835 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1476 = 1 • support1478 := by
  have hs : support1476 = fromList transition1835Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1835Chunk0]
  have hn : (transition1835Raw0 : Multiset ℕ) = 1 • (supportNumbers1478 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1478] using hm

private def transition1836Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 640, 642, 648, 650, 768, 770, 776, 778]
private def transition1836Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 384, 386, 392, 394, 256, 258, 264, 266]
private theorem transition1836Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1836Input0) = fromList transition1836Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1836 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0255 = 1 • support0103 := by
  have hs : support0255 = fromList transition1836Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1836Chunk0]
  have hn : (transition1836Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition1837Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 640, 642, 648, 650, 768, 770, 776, 778]
private def transition1837Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 128, 512, 130, 514, 136, 520, 138, 522, 384, 768, 386, 770, 392, 776, 394, 778, 256, 896, 258, 898, 264, 904, 266, 906]
private theorem transition1837Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1837Input0) = fromList transition1837Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1837 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0255 = 1 • support0104 := by
  have hs : support0255 = fromList transition1837Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1837Chunk0]
  have hn : (transition1837Raw0 : Multiset ℕ) = 1 • (supportNumbers0104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0104] using hm

private def transition1838Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 640, 642, 648, 650, 768, 770, 776, 778]
private def transition1838Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 384, 386, 392, 394, 256, 258, 264, 266]
private theorem transition1838Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1838Input0) = fromList transition1838Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1838 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0255 = 1 • support0103 := by
  have hs : support0255 = fromList transition1838Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1838Chunk0]
  have hn : (transition1838Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition1839Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 640, 642, 648, 650, 768, 770, 776, 778]
private def transition1839Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 128, 672, 130, 674, 136, 680, 138, 682, 384, 928, 386, 930, 392, 936, 394, 938, 256, 800, 258, 802, 264, 808, 266, 810]
private theorem transition1839Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1839Input0) = fromList transition1839Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1839 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0255 = 1 • support0816 := by
  have hs : support0255 = fromList transition1839Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1839Chunk0]
  have hn : (transition1839Raw0 : Multiset ℕ) = 1 • (supportNumbers0816 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0816] using hm

private def transition1840Input0 : List ℕ := [0, 2, 8, 10, 640, 642, 648, 650]
private def transition1840Raw0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private theorem transition1840Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1840Input0) = fromList transition1840Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1840 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0256 = 1 • support0254 := by
  have hs : support0256 = fromList transition1840Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1840Chunk0]
  have hn : (transition1840Raw0 : Multiset ℕ) = 1 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1841Input0 : List ℕ := [0, 2, 8, 10, 640, 642, 648, 650]
private def transition1841Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition1841Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1841Input0) = fromList transition1841Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1841 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0256 = 1 • support0255 := by
  have hs : support0256 = fromList transition1841Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1841Chunk0]
  have hn : (transition1841Raw0 : Multiset ℕ) = 1 • (supportNumbers0255 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0255] using hm

private def transition1842Input0 : List ℕ := [0, 2, 8, 10, 640, 642, 648, 650]
private def transition1842Raw0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private theorem transition1842Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1842Input0) = fromList transition1842Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1842 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0256 = 1 • support0254 := by
  have hs : support0256 = fromList transition1842Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1842Chunk0]
  have hn : (transition1842Raw0 : Multiset ℕ) = 1 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1843Input0 : List ℕ := [0, 2, 8, 10, 640, 642, 648, 650]
private def transition1843Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition1843Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1843Input0) = fromList transition1843Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1843 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0256 = 1 • support1272 := by
  have hs : support0256 = fromList transition1843Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1843Chunk0]
  have hn : (transition1843Raw0 : Multiset ℕ) = 1 • (supportNumbers1272 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1272] using hm

private def transition1844Input0 : List ℕ := [0, 2, 128, 130, 520, 522, 648, 650]
private def transition1844Raw0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private theorem transition1844Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1844Input0) = fromList transition1844Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1844 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0257 = 1 • support0345 := by
  have hs : support0257 = fromList transition1844Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1844Chunk0]
  have hn : (transition1844Raw0 : Multiset ℕ) = 1 • (supportNumbers0345 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0345] using hm

private def transition1845Input0 : List ℕ := [0, 2, 128, 130, 520, 522, 648, 650]
private def transition1845Raw0 : List ℕ := [0, 640, 2, 642, 128, 512, 130, 514, 264, 904, 266, 906, 392, 776, 394, 778]
private theorem transition1845Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1845Input0) = fromList transition1845Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1845 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0257 = 1 • support0346 := by
  have hs : support0257 = fromList transition1845Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1845Chunk0]
  have hn : (transition1845Raw0 : Multiset ℕ) = 1 • (supportNumbers0346 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0346] using hm

private def transition1846Input0 : List ℕ := [0, 2, 128, 130, 520, 522, 648, 650]
private def transition1846Raw0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private theorem transition1846Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1846Input0) = fromList transition1846Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1846 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0257 = 1 • support0345 := by
  have hs : support0257 = fromList transition1846Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1846Chunk0]
  have hn : (transition1846Raw0 : Multiset ℕ) = 1 • (supportNumbers0345 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0345] using hm

private def transition1847Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition1847Raw0 : List ℕ := [0, 128, 10, 138]
private theorem transition1847Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1847Input0) = fromList transition1847Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1847 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0345 = 1 • support1480 := by
  have hs : support0345 = fromList transition1847Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1847Chunk0]
  have hn : (transition1847Raw0 : Multiset ℕ) = 1 • (supportNumbers1480 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1480] using hm

private def transition1848Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition1848Raw0 : List ℕ := [0, 578, 128, 706, 584, 10, 712, 138]
private theorem transition1848Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1848Input0) = fromList transition1848Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1848 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0345 = 1 • support1481 := by
  have hs : support0345 = fromList transition1848Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1848Chunk0]
  have hn : (transition1848Raw0 : Multiset ℕ) = 1 • (supportNumbers1481 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1481] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
