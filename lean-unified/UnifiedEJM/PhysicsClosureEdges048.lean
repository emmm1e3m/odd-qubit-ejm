import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0742Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0742Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0742Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0742Input0) = fromList transition0742Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0742Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0742Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0742Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0742Input1) = fromList transition0742Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0742Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 680, 681, 682, 683, 684, 685, 686, 687, 696, 697, 698, 699, 700, 701, 702, 703, 744, 745, 746, 747, 748, 749, 750, 751, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition0742Raw2 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition0742Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0742Input2) = fromList transition0742Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0742Input3 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 824, 825, 826, 827, 828, 829, 830, 831, 872, 873, 874, 875, 876, 877, 878, 879, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition0742Raw3 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition0742Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0742Input3) = fromList transition0742Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0742 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1009 = 1 • support0540 := by
  have hs : support1009 = fromList transition0742Input0 + fromList transition0742Input1 + fromList transition0742Input2 + fromList transition0742Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0742Chunk0, transition0742Chunk1, transition0742Chunk2, transition0742Chunk3]
  have hn : (transition0742Raw0 : Multiset ℕ) + (transition0742Raw1 : Multiset ℕ) + (transition0742Raw2 : Multiset ℕ) + (transition0742Raw3 : Multiset ℕ) = 1 • (supportNumbers0540 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0540] using hm

private def transition0743Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0743Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition0743Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0743Input0) = fromList transition0743Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0743Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0743Raw1 : List ℕ := [8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663]
private theorem transition0743Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0743Input1) = fromList transition0743Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0743Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 680, 681, 682, 683, 684, 685, 686, 687, 696, 697, 698, 699, 700, 701, 702, 703, 744, 745, 746, 747, 748, 749, 750, 751, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition0743Raw2 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0743Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0743Input2) = fromList transition0743Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0743Input3 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 824, 825, 826, 827, 828, 829, 830, 831, 872, 873, 874, 875, 876, 877, 878, 879, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition0743Raw3 : List ℕ := [296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition0743Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0743Input3) = fromList transition0743Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0743 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1009 = 1 • support0542 := by
  have hs : support1009 = fromList transition0743Input0 + fromList transition0743Input1 + fromList transition0743Input2 + fromList transition0743Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0743Chunk0, transition0743Chunk1, transition0743Chunk2, transition0743Chunk3]
  have hn : (transition0743Raw0 : Multiset ℕ) + (transition0743Raw1 : Multiset ℕ) + (transition0743Raw2 : Multiset ℕ) + (transition0743Raw3 : Multiset ℕ) = 1 • (supportNumbers0542 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0542] using hm

private def transition0744Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0744Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0744Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0744Input0) = fromList transition0744Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0744Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0744Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0744Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0744Input1) = fromList transition0744Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0744 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0096 = 1 • support0164 := by
  have hs : support0096 = fromList transition0744Input0 + fromList transition0744Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0744Chunk0, transition0744Chunk1]
  have hn : (transition0744Raw0 : Multiset ℕ) + (transition0744Raw1 : Multiset ℕ) = 1 • (supportNumbers0164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0164] using hm

private def transition0745Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0745Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 16, 17, 18, 19, 20, 21, 22, 23, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 80, 81, 82, 83, 84, 85, 86, 87, 728, 729, 730, 731, 732, 733, 734, 735]
private theorem transition0745Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0745Input0) = fromList transition0745Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0745Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0745Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 520, 521, 522, 523, 524, 525, 526, 527, 144, 145, 146, 147, 148, 149, 150, 151, 536, 537, 538, 539, 540, 541, 542, 543, 192, 193, 194, 195, 196, 197, 198, 199, 584, 585, 586, 587, 588, 589, 590, 591, 208, 209, 210, 211, 212, 213, 214, 215, 600, 601, 602, 603, 604, 605, 606, 607]
private theorem transition0745Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0745Input1) = fromList transition0745Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0745 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0096 = 1 • support0165 := by
  have hs : support0096 = fromList transition0745Input0 + fromList transition0745Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0745Chunk0, transition0745Chunk1]
  have hn : (transition0745Raw0 : Multiset ℕ) + (transition0745Raw1 : Multiset ℕ) = 1 • (supportNumbers0165 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0165] using hm

private def transition0746Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0746Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0746Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0746Input0) = fromList transition0746Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0746Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0746Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0746Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0746Input1) = fromList transition0746Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0746 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0096 = 1 • support0164 := by
  have hs : support0096 = fromList transition0746Input0 + fromList transition0746Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0746Chunk0, transition0746Chunk1]
  have hn : (transition0746Raw0 : Multiset ℕ) + (transition0746Raw1 : Multiset ℕ) = 1 • (supportNumbers0164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0164] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
