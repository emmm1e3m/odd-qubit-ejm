import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0187Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0187Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543]
private theorem transition0187Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input0) = fromList transition0187Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0187Raw1 : List ℕ := [128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition0187Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input1) = fromList transition0187Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0187Raw2 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543]
private theorem transition0187Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input2) = fromList transition0187Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input3 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0187Raw3 : List ℕ := [128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition0187Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input3) = fromList transition0187Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input4 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition0187Raw4 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831]
private theorem transition0187Chunk4 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input4) = fromList transition0187Raw4 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input5 : List ℕ := [672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition0187Raw5 : List ℕ := [416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0187Chunk5 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input5) = fromList transition0187Raw5 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input6 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]
private def transition0187Raw6 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831]
private theorem transition0187Chunk6 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input6) = fromList transition0187Raw6 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0187Input7 : List ℕ := [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0187Raw7 : List ℕ := [416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0187Chunk7 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0187Input7) = fromList transition0187Raw7 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0187 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0643 = 2 • support0542 := by
  have hs : support0643 = fromList transition0187Input0 + fromList transition0187Input1 + fromList transition0187Input2 + fromList transition0187Input3 + fromList transition0187Input4 + fromList transition0187Input5 + fromList transition0187Input6 + fromList transition0187Input7 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0187Chunk0, transition0187Chunk1, transition0187Chunk2, transition0187Chunk3, transition0187Chunk4, transition0187Chunk5, transition0187Chunk6, transition0187Chunk7]
  have hn : (transition0187Raw0 : Multiset ℕ) + (transition0187Raw1 : Multiset ℕ) + (transition0187Raw2 : Multiset ℕ) + (transition0187Raw3 : Multiset ℕ) + (transition0187Raw4 : Multiset ℕ) + (transition0187Raw5 : Multiset ℕ) + (transition0187Raw6 : Multiset ℕ) + (transition0187Raw7 : Multiset ℕ) = 2 • (supportNumbers0542 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0542] using hm

private def transition0188Input0 : List ℕ := [0, 2]
private def transition0188Raw0 : List ℕ := [0, 2]
private theorem transition0188Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0188Input0) = fromList transition0188Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0188 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0188Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0188Chunk0]
  have hn : (transition0188Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0189Input0 : List ℕ := [0, 2]
private def transition0189Raw0 : List ℕ := [0, 640, 2, 642]
private theorem transition0189Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0189Input0) = fromList transition0189Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0189 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0008 = 1 • support0052 := by
  have hs : support0008 = fromList transition0189Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0189Chunk0]
  have hn : (transition0189Raw0 : Multiset ℕ) = 1 • (supportNumbers0052 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0052] using hm

private def transition0190Input0 : List ℕ := [0, 2]
private def transition0190Raw0 : List ℕ := [0, 2]
private theorem transition0190Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0190Input0) = fromList transition0190Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0190 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0190Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0190Chunk0]
  have hn : (transition0190Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0191Input0 : List ℕ := [0, 2]
private def transition0191Raw0 : List ℕ := [0, 544, 2, 546]
private theorem transition0191Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0191Input0) = fromList transition0191Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0191 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0008 = 1 • support0644 := by
  have hs : support0008 = fromList transition0191Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0191Chunk0]
  have hn : (transition0191Raw0 : Multiset ℕ) = 1 • (supportNumbers0644 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0644] using hm

private def transition0192Input0 : List ℕ := [0, 2, 544, 546]
private def transition0192Raw0 : List ℕ := [0, 2, 288, 290]
private theorem transition0192Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0192Input0) = fromList transition0192Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0192 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0644 = 1 • support0645 := by
  have hs : support0644 = fromList transition0192Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0192Chunk0]
  have hn : (transition0192Raw0 : Multiset ℕ) = 1 • (supportNumbers0645 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0645] using hm

private def transition0193Input0 : List ℕ := [0, 2, 544, 546]
private def transition0193Raw0 : List ℕ := [0, 576, 2, 578, 288, 864, 290, 866]
private theorem transition0193Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0193Input0) = fromList transition0193Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0193 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0644 = 1 • support0646 := by
  have hs : support0644 = fromList transition0193Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0193Chunk0]
  have hn : (transition0193Raw0 : Multiset ℕ) = 1 • (supportNumbers0646 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0646] using hm

private def transition0194Input0 : List ℕ := [0, 2, 392, 394]
private def transition0194Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0194Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0194Input0) = fromList transition0194Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0194 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0024 = 1 • support0053 := by
  have hs : support0024 = fromList transition0194Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0194Chunk0]
  have hn : (transition0194Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0195Input0 : List ℕ := [0, 2, 392, 394]
private def transition0195Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0195Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0195Input0) = fromList transition0195Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0195 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0024 = 1 • support0053 := by
  have hs : support0024 = fromList transition0195Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0195Chunk0]
  have hn : (transition0195Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0196Input0 : List ℕ := [0, 2, 392, 394]
private def transition0196Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0196Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0196Input0) = fromList transition0196Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0196 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0024 = 1 • support0053 := by
  have hs : support0024 = fromList transition0196Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0196Chunk0]
  have hn : (transition0196Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0197Input0 : List ℕ := [0, 2, 136, 138]
private def transition0197Raw0 : List ℕ := [0, 136]
private theorem transition0197Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0197Input0) = fromList transition0197Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0197 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0053 = 1 • support0648 := by
  have hs : support0053 = fromList transition0197Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0197Chunk0]
  have hn : (transition0197Raw0 : Multiset ℕ) = 1 • (supportNumbers0648 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0648] using hm

private def transition0198Input0 : List ℕ := [0, 2, 136, 138]
private def transition0198Raw0 : List ℕ := [0, 578, 136, 714]
private theorem transition0198Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0198Input0) = fromList transition0198Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0198 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0053 = 1 • support0649 := by
  have hs : support0053 = fromList transition0198Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0198Chunk0]
  have hn : (transition0198Raw0 : Multiset ℕ) = 1 • (supportNumbers0649 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0649] using hm

private def transition0199Input0 : List ℕ := [0, 2, 392, 394]
private def transition0199Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0199Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0199Input0) = fromList transition0199Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0199 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0024 = 1 • support0053 := by
  have hs : support0024 = fromList transition0199Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0199Chunk0]
  have hn : (transition0199Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0200Input0 : List ℕ := [0, 2, 136, 138]
private def transition0200Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0200Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0200Input0) = fromList transition0200Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0200 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0053 = 1 • support0053 := by
  have hs : support0053 = fromList transition0200Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0200Chunk0]
  have hn : (transition0200Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0201Input0 : List ℕ := [0, 2, 136, 138]
private def transition0201Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714]
private theorem transition0201Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0201Input0) = fromList transition0201Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0201 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0053 = 1 • support0651 := by
  have hs : support0053 = fromList transition0201Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0201Chunk0]
  have hn : (transition0201Raw0 : Multiset ℕ) = 1 • (supportNumbers0651 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0651] using hm

private def transition0202Input0 : List ℕ := [0, 2, 392, 394, 640, 642, 776, 778]
private def transition0202Raw0 : List ℕ := [0, 2, 136, 138, 384, 386, 264, 266]
private theorem transition0202Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0202Input0) = fromList transition0202Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0202 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0025 = 1 • support0054 := by
  have hs : support0025 = fromList transition0202Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0202Chunk0]
  have hn : (transition0202Raw0 : Multiset ℕ) = 1 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition0203Input0 : List ℕ := [0, 2, 392, 394, 640, 642, 776, 778]
private def transition0203Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 384, 768, 386, 770, 264, 904, 266, 906]
private theorem transition0203Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0203Input0) = fromList transition0203Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0203 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0025 = 1 • support0055 := by
  have hs : support0025 = fromList transition0203Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0203Chunk0]
  have hn : (transition0203Raw0 : Multiset ℕ) = 1 • (supportNumbers0055 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0055] using hm

private def transition0204Input0 : List ℕ := [0, 2, 392, 394, 640, 642, 776, 778]
private def transition0204Raw0 : List ℕ := [0, 2, 136, 138, 384, 386, 264, 266]
private theorem transition0204Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0204Input0) = fromList transition0204Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0204 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0025 = 1 • support0054 := by
  have hs : support0025 = fromList transition0204Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0204Chunk0]
  have hn : (transition0204Raw0 : Multiset ℕ) = 1 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition0205Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0205Raw0 : List ℕ := [0, 136, 10, 130]
private theorem transition0205Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0205Input0) = fromList transition0205Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0205 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0054 = 1 • support0653 := by
  have hs : support0054 = fromList transition0205Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0205Chunk0]
  have hn : (transition0205Raw0 : Multiset ℕ) = 1 • (supportNumbers0653 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0653] using hm

private def transition0206Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private def transition0206Raw0 : List ℕ := [0, 578, 136, 714, 584, 10, 704, 130]
private theorem transition0206Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0206Input0) = fromList transition0206Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0206 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0054 = 1 • support0654 := by
  have hs : support0054 = fromList transition0206Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0206Chunk0]
  have hn : (transition0206Raw0 : Multiset ℕ) = 1 • (supportNumbers0654 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0654] using hm

private def transition0207Input0 : List ℕ := [0, 2, 392, 394, 640, 642, 776, 778]
private def transition0207Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 384, 928, 386, 930, 264, 808, 266, 810]
private theorem transition0207Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0207Input0) = fromList transition0207Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0207 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0025 = 1 • support0656 := by
  have hs : support0025 = fromList transition0207Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0207Chunk0]
  have hn : (transition0207Raw0 : Multiset ℕ) = 1 • (supportNumbers0656 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0656] using hm

private def transition0208Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 544, 546, 680, 682, 808, 810, 928, 930]
private def transition0208Raw0 : List ℕ := [0, 2, 136, 138, 8, 10, 128, 130, 288, 290, 424, 426, 296, 298, 416, 418]
private theorem transition0208Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0208Input0) = fromList transition0208Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0208 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0656 = 1 • support0657 := by
  have hs : support0656 = fromList transition0208Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0208Chunk0]
  have hn : (transition0208Raw0 : Multiset ℕ) = 1 • (supportNumbers0657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0657] using hm

private def transition0209Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 544, 546, 680, 682, 808, 810, 928, 930]
private def transition0209Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 8, 584, 10, 586, 128, 704, 130, 706, 288, 864, 290, 866, 424, 1000, 426, 1002, 296, 872, 298, 874, 416, 992, 418, 994]
private theorem transition0209Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0209Input0) = fromList transition0209Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0209 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0656 = 1 • support0658 := by
  have hs : support0656 = fromList transition0209Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0209Chunk0]
  have hn : (transition0209Raw0 : Multiset ℕ) = 1 • (supportNumbers0658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0658] using hm

private def transition0210Input0 : List ℕ := [0, 2, 137, 139]
private def transition0210Raw0 : List ℕ := [0, 2]
private theorem transition0210Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0210Input0) = fromList transition0210Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0210 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0026 = 1 • support0008 := by
  have hs : support0026 = fromList transition0210Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0210Chunk0]
  have hn : (transition0210Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0211Input0 : List ℕ := [0, 2, 137, 139]
private def transition0211Raw0 : List ℕ := [0, 2, 521, 523]
private theorem transition0211Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0211Input0) = fromList transition0211Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0211 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0026 = 1 • support0056 := by
  have hs : support0026 = fromList transition0211Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0211Chunk0]
  have hn : (transition0211Raw0 : Multiset ℕ) = 1 • (supportNumbers0056 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0056] using hm

private def transition0212Input0 : List ℕ := [0, 2, 137, 139]
private def transition0212Raw0 : List ℕ := [0, 2]
private theorem transition0212Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0212Input0) = fromList transition0212Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0212 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0026 = 1 • support0008 := by
  have hs : support0026 = fromList transition0212Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0212Chunk0]
  have hn : (transition0212Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0213Input0 : List ℕ := [0, 2, 137, 139]
private def transition0213Raw0 : List ℕ := [0, 2, 681, 683]
private theorem transition0213Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0213Input0) = fromList transition0213Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0213 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0026 = 1 • support0660 := by
  have hs : support0026 = fromList transition0213Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0213Chunk0]
  have hn : (transition0213Raw0 : Multiset ℕ) = 1 • (supportNumbers0660 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0660] using hm

private def transition0214Input0 : List ℕ := [0, 2, 681, 683]
private def transition0214Raw0 : List ℕ := [0, 2, 425, 427]
private theorem transition0214Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0214Input0) = fromList transition0214Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0214 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0660 = 1 • support0661 := by
  have hs : support0660 = fromList transition0214Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0214Chunk0]
  have hn : (transition0214Raw0 : Multiset ℕ) = 1 • (supportNumbers0661 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0661] using hm

private def transition0215Input0 : List ℕ := [0, 2, 681, 683]
private def transition0215Raw0 : List ℕ := [0, 576, 2, 578, 425, 1001, 427, 1003]
private theorem transition0215Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0215Input0) = fromList transition0215Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0215 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0660 = 1 • support0662 := by
  have hs : support0660 = fromList transition0215Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0215Chunk0]
  have hn : (transition0215Raw0 : Multiset ℕ) = 1 • (supportNumbers0662 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0662] using hm

private def transition0216Input0 : List ℕ := [0, 2, 137, 139, 513, 515, 648, 650]
private def transition0216Raw0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private theorem transition0216Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0216Input0) = fromList transition0216Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0216 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0027 = 1 • support0057 := by
  have hs : support0027 = fromList transition0216Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0216Chunk0]
  have hn : (transition0216Raw0 : Multiset ℕ) = 1 • (supportNumbers0057 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0057] using hm

private def transition0217Input0 : List ℕ := [0, 2, 137, 139, 513, 515, 648, 650]
private def transition0217Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 257, 897, 259, 899, 392, 776, 394, 778]
private theorem transition0217Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0217Input0) = fromList transition0217Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0217 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0027 = 1 • support0058 := by
  have hs : support0027 = fromList transition0217Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0217Chunk0]
  have hn : (transition0217Raw0 : Multiset ℕ) = 1 • (supportNumbers0058 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0058] using hm

private def transition0218Input0 : List ℕ := [0, 2, 137, 139, 513, 515, 648, 650]
private def transition0218Raw0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private theorem transition0218Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0218Input0) = fromList transition0218Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0218 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0027 = 1 • support0057 := by
  have hs : support0027 = fromList transition0218Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0218Chunk0]
  have hn : (transition0218Raw0 : Multiset ℕ) = 1 • (supportNumbers0057 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0057] using hm

private def transition0219Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0219Raw0 : List ℕ := [0, 137, 3, 138]
private theorem transition0219Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0219Input0) = fromList transition0219Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0219 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0057 = 1 • support0664 := by
  have hs : support0057 = fromList transition0219Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0219Chunk0]
  have hn : (transition0219Raw0 : Multiset ℕ) = 1 • (supportNumbers0664 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0664] using hm

private def transition0220Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0220Raw0 : List ℕ := [0, 578, 137, 715, 577, 3, 712, 138]
private theorem transition0220Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0220Input0) = fromList transition0220Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0220 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0057 = 1 • support0665 := by
  have hs : support0057 = fromList transition0220Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0220Chunk0]
  have hn : (transition0220Raw0 : Multiset ℕ) = 1 • (supportNumbers0665 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0665] using hm

private def transition0221Input0 : List ℕ := [0, 2, 137, 139, 513, 515, 648, 650]
private def transition0221Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 257, 801, 259, 803, 392, 936, 394, 938]
private theorem transition0221Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0221Input0) = fromList transition0221Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0221 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0027 = 1 • support0667 := by
  have hs : support0027 = fromList transition0221Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0221Chunk0]
  have hn : (transition0221Raw0 : Multiset ℕ) = 1 • (supportNumbers0667 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0667] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
