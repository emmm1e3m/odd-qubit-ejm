import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0063Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0063Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543]
private theorem transition0063Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0063Input0) = fromList transition0063Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0063Input1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0063Raw1 : List ℕ := [128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition0063Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0063Input1) = fromList transition0063Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0063Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition0063Raw2 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831]
private theorem transition0063Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0063Input2) = fromList transition0063Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0063Input3 : List ℕ := [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0063Raw3 : List ℕ := [416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0063Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0063Input3) = fromList transition0063Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0063 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0539 = 1 • support0542 := by
  have hs : support0539 = fromList transition0063Input0 + fromList transition0063Input1 + fromList transition0063Input2 + fromList transition0063Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0063Chunk0, transition0063Chunk1, transition0063Chunk2, transition0063Chunk3]
  have hn : (transition0063Raw0 : Multiset ℕ) + (transition0063Raw1 : Multiset ℕ) + (transition0063Raw2 : Multiset ℕ) + (transition0063Raw3 : Multiset ℕ) = 1 • (supportNumbers0542 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0542] using hm

private def transition0064Input0 : List ℕ := [0, 2]
private def transition0064Raw0 : List ℕ := [0, 2]
private theorem transition0064Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0064Input0) = fromList transition0064Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0064 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0064Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0064Chunk0]
  have hn : (transition0064Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0065Input0 : List ℕ := [0, 2]
private def transition0065Raw0 : List ℕ := [0, 2]
private theorem transition0065Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0065Input0) = fromList transition0065Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0065 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0065Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0065Chunk0]
  have hn : (transition0065Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0066Input0 : List ℕ := [0, 2]
private def transition0066Raw0 : List ℕ := [0, 2]
private theorem transition0066Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0066Input0) = fromList transition0066Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0066 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0066Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0066Chunk0]
  have hn : (transition0066Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0067Input0 : List ℕ := [0, 2]
private def transition0067Raw0 : List ℕ := [0, 2]
private theorem transition0067Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0067Input0) = fromList transition0067Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0067 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0067Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0067Chunk0]
  have hn : (transition0067Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0068Input0 : List ℕ := [0, 2]
private def transition0068Raw0 : List ℕ := [0, 2]
private theorem transition0068Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0068Input0) = fromList transition0068Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0068 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0008 = 1 • support0008 := by
  have hs : support0008 = fromList transition0068Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0068Chunk0]
  have hn : (transition0068Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0069Input0 : List ℕ := [0, 2]
private def transition0069Raw0 : List ℕ := [0, 576, 2, 578]
private theorem transition0069Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0069Input0) = fromList transition0069Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0069 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0008 = 1 • support0544 := by
  have hs : support0008 = fromList transition0069Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0069Chunk0]
  have hn : (transition0069Raw0 : Multiset ℕ) = 1 • (supportNumbers0544 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0544] using hm

private def transition0070Input0 : List ℕ := [0, 2, 648, 650]
private def transition0070Raw0 : List ℕ := [0, 2, 392, 394]
private theorem transition0070Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0070Input0) = fromList transition0070Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0070 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0009 = 1 • support0024 := by
  have hs : support0009 = fromList transition0070Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0070Chunk0]
  have hn : (transition0070Raw0 : Multiset ℕ) = 1 • (supportNumbers0024 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0024] using hm

private def transition0071Input0 : List ℕ := [0, 2, 648, 650]
private def transition0071Raw0 : List ℕ := [0, 640, 2, 642, 392, 776, 394, 778]
private theorem transition0071Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0071Input0) = fromList transition0071Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0071 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0009 = 1 • support0025 := by
  have hs : support0009 = fromList transition0071Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0071Chunk0]
  have hn : (transition0071Raw0 : Multiset ℕ) = 1 • (supportNumbers0025 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0025] using hm

private def transition0072Input0 : List ℕ := [0, 2, 648, 650]
private def transition0072Raw0 : List ℕ := [0, 2, 392, 394]
private theorem transition0072Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0072Input0) = fromList transition0072Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0072 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0009 = 1 • support0024 := by
  have hs : support0009 = fromList transition0072Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0072Chunk0]
  have hn : (transition0072Raw0 : Multiset ℕ) = 1 • (supportNumbers0024 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0024] using hm

private def transition0073Input0 : List ℕ := [0, 2, 392, 394]
private def transition0073Raw0 : List ℕ := [0, 138]
private theorem transition0073Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0073Input0) = fromList transition0073Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0073 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0024 = 1 • support0546 := by
  have hs : support0024 = fromList transition0073Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0073Chunk0]
  have hn : (transition0073Raw0 : Multiset ℕ) = 1 • (supportNumbers0546 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0546] using hm

private def transition0074Input0 : List ℕ := [0, 2, 392, 394]
private def transition0074Raw0 : List ℕ := [0, 578, 712, 138]
private theorem transition0074Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0074Input0) = fromList transition0074Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0074 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0024 = 1 • support0547 := by
  have hs : support0024 = fromList transition0074Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0074Chunk0]
  have hn : (transition0074Raw0 : Multiset ℕ) = 1 • (supportNumbers0547 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0547] using hm

private def transition0075Input0 : List ℕ := [0, 2, 648, 650]
private def transition0075Raw0 : List ℕ := [0, 544, 2, 546, 392, 936, 394, 938]
private theorem transition0075Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0075Input0) = fromList transition0075Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0075 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0009 = 1 • support0549 := by
  have hs : support0009 = fromList transition0075Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0075Chunk0]
  have hn : (transition0075Raw0 : Multiset ℕ) = 1 • (supportNumbers0549 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0549] using hm

private def transition0076Input0 : List ℕ := [0, 2, 392, 394, 544, 546, 936, 938]
private def transition0076Raw0 : List ℕ := [0, 2, 136, 138, 288, 290, 424, 426]
private theorem transition0076Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0076Input0) = fromList transition0076Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0076 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0549 = 1 • support0550 := by
  have hs : support0549 = fromList transition0076Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0076Chunk0]
  have hn : (transition0076Raw0 : Multiset ℕ) = 1 • (supportNumbers0550 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0550] using hm

private def transition0077Input0 : List ℕ := [0, 2, 392, 394, 544, 546, 936, 938]
private def transition0077Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 288, 864, 290, 866, 424, 1000, 426, 1002]
private theorem transition0077Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0077Input0) = fromList transition0077Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0077 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0549 = 1 • support0551 := by
  have hs : support0549 = fromList transition0077Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0077Chunk0]
  have hn : (transition0077Raw0 : Multiset ℕ) = 1 • (supportNumbers0551 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0551] using hm

private def transition0078Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0078Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition0078Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0078Input0) = fromList transition0078Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0078 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0010 = 1 • support0026 := by
  have hs : support0010 = fromList transition0078Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0078Chunk0]
  have hn : (transition0078Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition0079Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0079Raw0 : List ℕ := [0, 2, 648, 650, 513, 515, 137, 139]
private theorem transition0079Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0079Input0) = fromList transition0079Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0079 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0010 = 1 • support0027 := by
  have hs : support0010 = fromList transition0079Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0079Chunk0]
  have hn : (transition0079Raw0 : Multiset ℕ) = 1 • (supportNumbers0027 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0027] using hm

private def transition0080Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0080Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition0080Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0080Input0) = fromList transition0080Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0080 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0010 = 1 • support0026 := by
  have hs : support0010 = fromList transition0080Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0080Chunk0]
  have hn : (transition0080Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition0081Input0 : List ℕ := [0, 2, 137, 139]
private def transition0081Raw0 : List ℕ := [0, 137]
private theorem transition0081Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0081Input0) = fromList transition0081Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0081 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0026 = 1 • support0553 := by
  have hs : support0026 = fromList transition0081Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0081Chunk0]
  have hn : (transition0081Raw0 : Multiset ℕ) = 1 • (supportNumbers0553 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0553] using hm

private def transition0082Input0 : List ℕ := [0, 2, 137, 139]
private def transition0082Raw0 : List ℕ := [0, 578, 137, 715]
private theorem transition0082Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0082Input0) = fromList transition0082Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0082 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0026 = 1 • support0554 := by
  have hs : support0026 = fromList transition0082Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0082Chunk0]
  have hn : (transition0082Raw0 : Multiset ℕ) = 1 • (supportNumbers0554 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0554] using hm

private def transition0083Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0083Raw0 : List ℕ := [0, 2, 552, 554, 673, 675, 137, 139]
private theorem transition0083Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0083Input0) = fromList transition0083Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0083 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0010 = 1 • support0556 := by
  have hs : support0010 = fromList transition0083Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0083Chunk0]
  have hn : (transition0083Raw0 : Multiset ℕ) = 1 • (supportNumbers0556 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0556] using hm

private def transition0084Input0 : List ℕ := [0, 2, 137, 139, 552, 554, 673, 675]
private def transition0084Raw0 : List ℕ := [0, 2, 137, 139, 296, 298, 417, 419]
private theorem transition0084Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0084Input0) = fromList transition0084Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0084 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0556 = 1 • support0557 := by
  have hs : support0556 = fromList transition0084Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0084Chunk0]
  have hn : (transition0084Raw0 : Multiset ℕ) = 1 • (supportNumbers0557 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0557] using hm

private def transition0085Input0 : List ℕ := [0, 2, 137, 139, 552, 554, 673, 675]
private def transition0085Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 296, 872, 298, 874, 417, 993, 419, 995]
private theorem transition0085Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0085Input0) = fromList transition0085Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0085 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0556 = 1 • support0558 := by
  have hs : support0556 = fromList transition0085Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0085Chunk0]
  have hn : (transition0085Raw0 : Multiset ℕ) = 1 • (supportNumbers0558 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0558] using hm

private def transition0086Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 640, 642, 648, 650, 769, 771, 777, 779]
private def transition0086Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 384, 386, 392, 394, 257, 259, 265, 267]
private theorem transition0086Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0086Input0) = fromList transition0086Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0086 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0011 = 1 • support0028 := by
  have hs : support0011 = fromList transition0086Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0086Chunk0]
  have hn : (transition0086Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition0087Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 640, 642, 648, 650, 769, 771, 777, 779]
private def transition0087Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 384, 768, 386, 770, 392, 776, 394, 778, 257, 897, 259, 899, 265, 905, 267, 907]
private theorem transition0087Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0087Input0) = fromList transition0087Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0087 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0011 = 1 • support0029 := by
  have hs : support0011 = fromList transition0087Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0087Chunk0]
  have hn : (transition0087Raw0 : Multiset ℕ) = 1 • (supportNumbers0029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0029] using hm

private def transition0088Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 640, 642, 648, 650, 769, 771, 777, 779]
private def transition0088Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 384, 386, 392, 394, 257, 259, 265, 267]
private theorem transition0088Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0088Input0) = fromList transition0088Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0088 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0011 = 1 • support0028 := by
  have hs : support0011 = fromList transition0088Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0088Chunk0]
  have hn : (transition0088Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition0089Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0089Raw0 : List ℕ := [0, 8, 129, 137, 3, 11, 130, 138]
private theorem transition0089Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0089Input0) = fromList transition0089Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0089 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0028 = 1 • support0560 := by
  have hs : support0028 = fromList transition0089Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0089Chunk0]
  have hn : (transition0089Raw0 : Multiset ℕ) = 1 • (supportNumbers0560 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0560] using hm

private def transition0090Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0090Raw0 : List ℕ := [0, 578, 8, 586, 129, 707, 137, 715, 577, 3, 585, 11, 704, 130, 712, 138]
private theorem transition0090Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0090Input0) = fromList transition0090Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0090 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0028 = 1 • support0561 := by
  have hs : support0028 = fromList transition0090Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0090Chunk0]
  have hn : (transition0090Raw0 : Multiset ℕ) = 1 • (supportNumbers0561 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0561] using hm

private def transition0091Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 640, 642, 648, 650, 769, 771, 777, 779]
private def transition0091Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 384, 928, 386, 930, 392, 936, 394, 938, 257, 801, 259, 803, 265, 809, 267, 811]
private theorem transition0091Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0091Input0) = fromList transition0091Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0091 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0011 = 1 • support0563 := by
  have hs : support0011 = fromList transition0091Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0091Chunk0]
  have hn : (transition0091Raw0 : Multiset ℕ) = 1 • (supportNumbers0563 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0563] using hm

private def transition0092Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 544, 546, 552, 554, 673, 675, 681, 683, 801, 803, 809, 811, 928, 930, 936, 938]
private def transition0092Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 1, 3, 9, 11, 128, 130, 136, 138, 288, 290, 296, 298, 417, 419, 425, 427, 289, 291, 297, 299, 416, 418, 424, 426]
private theorem transition0092Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0092Input0) = fromList transition0092Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0092 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0563 = 1 • support0564 := by
  have hs : support0563 = fromList transition0092Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0092Chunk0]
  have hn : (transition0092Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition0093Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 544, 546, 552, 554, 673, 675, 681, 683, 801, 803, 809, 811, 928, 930, 936, 938]
private def transition0093Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 1, 577, 3, 579, 9, 585, 11, 587, 128, 704, 130, 706, 136, 712, 138, 714, 288, 864, 290, 866, 296, 872, 298, 874, 417, 993, 419, 995, 425, 1001, 427, 1003, 289, 865, 291, 867, 297, 873, 299, 875, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition0093Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0093Input0) = fromList transition0093Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0093 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0563 = 1 • support0565 := by
  have hs : support0563 = fromList transition0093Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0093Chunk0]
  have hn : (transition0093Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition0094Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0094Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0094Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0094Input0) = fromList transition0094Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0094 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0012 = 1 • support0030 := by
  have hs : support0012 = fromList transition0094Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0094Chunk0]
  have hn : (transition0094Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0095Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0095Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671]
private theorem transition0095Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0095Input0) = fromList transition0095Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0095 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0012 = 1 • support0031 := by
  have hs : support0012 = fromList transition0095Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0095Chunk0]
  have hn : (transition0095Raw0 : Multiset ℕ) = 1 • (supportNumbers0031 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0031] using hm

private def transition0096Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0096Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0096Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0096Input0) = fromList transition0096Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0096 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0012 = 1 • support0030 := by
  have hs : support0012 = fromList transition0096Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0096Chunk0]
  have hn : (transition0096Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0097Input0 : List ℕ := [0, 1, 2, 3]
private def transition0097Raw0 : List ℕ := [0, 1]
private theorem transition0097Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0097Input0) = fromList transition0097Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0097 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0030 = 1 • support0493 := by
  have hs : support0030 = fromList transition0097Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0097Chunk0]
  have hn : (transition0097Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def transition0098Input0 : List ℕ := [0, 1, 2, 3]
private def transition0098Raw0 : List ℕ := [0, 1, 578, 579]
private theorem transition0098Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0098Input0) = fromList transition0098Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0098 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0030 = 1 • support0567 := by
  have hs : support0030 = fromList transition0098Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0098Chunk0]
  have hn : (transition0098Raw0 : Multiset ℕ) = 1 • (supportNumbers0567 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0567] using hm

private def transition0099Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0099Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575]
private theorem transition0099Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0099Input0) = fromList transition0099Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0099 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0012 = 1 • support0569 := by
  have hs : support0012 = fromList transition0099Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0099Chunk0]
  have hn : (transition0099Raw0 : Multiset ℕ) = 1 • (supportNumbers0569 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0569] using hm

private def transition0100Input0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575]
private def transition0100Raw0 : List ℕ := [0, 1, 2, 3, 316, 317, 318, 319]
private theorem transition0100Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0100Input0) = fromList transition0100Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0100 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0569 = 1 • support0570 := by
  have hs : support0569 = fromList transition0100Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0100Chunk0]
  have hn : (transition0100Raw0 : Multiset ℕ) = 1 • (supportNumbers0570 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0570] using hm

private def transition0101Input0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575]
private def transition0101Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition0101Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0101Input0) = fromList transition0101Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0101 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0569 = 1 • support0572 := by
  have hs : support0569 = fromList transition0101Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0101Chunk0]
  have hn : (transition0101Raw0 : Multiset ℕ) = 1 • (supportNumbers0572 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0572] using hm

private def transition0102Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition0102Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition0102Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0102Input0) = fromList transition0102Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0102 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0013 = 1 • support0032 := by
  have hs : support0013 = fromList transition0102Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0102Chunk0]
  have hn : (transition0102Raw0 : Multiset ℕ) = 1 • (supportNumbers0032 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0032] using hm

private def transition0103Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition0103Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition0103Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0103Input0) = fromList transition0103Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0103 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0013 = 1 • support0033 := by
  have hs : support0013 = fromList transition0103Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0103Chunk0]
  have hn : (transition0103Raw0 : Multiset ℕ) = 1 • (supportNumbers0033 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0033] using hm

private def transition0104Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition0104Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition0104Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0104Input0) = fromList transition0104Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0104 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0013 = 1 • support0032 := by
  have hs : support0013 = fromList transition0104Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0104Chunk0]
  have hn : (transition0104Raw0 : Multiset ℕ) = 1 • (supportNumbers0032 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0032] using hm

private def transition0105Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0105Raw0 : List ℕ := [0, 1, 28, 29, 138, 139, 150, 151]
private theorem transition0105Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0105Input0) = fromList transition0105Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0105 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0032 = 1 • support0574 := by
  have hs : support0032 = fromList transition0105Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0105Chunk0]
  have hn : (transition0105Raw0 : Multiset ℕ) = 1 • (supportNumbers0574 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0574] using hm

private def transition0106Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0106Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 712, 713, 138, 139, 724, 725, 150, 151]
private theorem transition0106Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0106Input0) = fromList transition0106Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0106 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0032 = 1 • support0576 := by
  have hs : support0032 = fromList transition0106Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0106Chunk0]
  have hn : (transition0106Raw0 : Multiset ℕ) = 1 • (supportNumbers0576 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0576] using hm

private def transition0107Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition0107Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition0107Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0107Input0) = fromList transition0107Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0107 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0013 = 1 • support0578 := by
  have hs : support0013 = fromList transition0107Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0107Chunk0]
  have hn : (transition0107Raw0 : Multiset ℕ) = 1 • (supportNumbers0578 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0578] using hm

private def transition0108Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 544, 545, 546, 547, 572, 573, 574, 575, 936, 937, 938, 939, 948, 949, 950, 951]
private def transition0108Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 288, 289, 290, 291, 316, 317, 318, 319, 424, 425, 426, 427, 436, 437, 438, 439]
private theorem transition0108Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0108Input0) = fromList transition0108Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0108 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0578 = 1 • support0579 := by
  have hs : support0578 = fromList transition0108Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0108Chunk0]
  have hn : (transition0108Raw0 : Multiset ℕ) = 1 • (supportNumbers0579 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0579] using hm

private def transition0109Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 544, 545, 546, 547, 572, 573, 574, 575, 936, 937, 938, 939, 948, 949, 950, 951]
private def transition0109Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition0109Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0109Input0) = fromList transition0109Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0109 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0578 = 1 • support0581 := by
  have hs : support0578 = fromList transition0109Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0109Chunk0]
  have hn : (transition0109Raw0 : Multiset ℕ) = 1 • (supportNumbers0581 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0581] using hm

private def transition0110Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0110Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0110Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0110Input0) = fromList transition0110Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0110 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0014 = 1 • support0034 := by
  have hs : support0014 = fromList transition0110Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0110Chunk0]
  have hn : (transition0110Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition0111Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0111Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 20, 21, 22, 23, 668, 669, 670, 671, 512, 513, 514, 515, 136, 137, 138, 139, 532, 533, 534, 535, 156, 157, 158, 159]
private theorem transition0111Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0111Input0) = fromList transition0111Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0111 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0014 = 1 • support0035 := by
  have hs : support0014 = fromList transition0111Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0111Chunk0]
  have hn : (transition0111Raw0 : Multiset ℕ) = 1 • (supportNumbers0035 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0035] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
