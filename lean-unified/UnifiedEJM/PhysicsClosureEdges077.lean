import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1227Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition1227Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663]
private theorem transition1227Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1227Input0) = fromList transition1227Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1227Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1227Raw1 : List ℕ := [8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition1227Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1227Input1) = fromList transition1227Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1227Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 672, 673, 674, 675, 676, 677, 678, 679, 688, 689, 690, 691, 692, 693, 694, 695, 736, 737, 738, 739, 740, 741, 742, 743, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition1227Raw2 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition1227Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1227Input2) = fromList transition1227Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1227Input3 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 824, 825, 826, 827, 828, 829, 830, 831, 872, 873, 874, 875, 876, 877, 878, 879, 888, 889, 890, 891, 892, 893, 894, 895, 936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition1227Raw3 : List ℕ := [296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition1227Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1227Input3) = fromList transition1227Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1227 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1263 = 1 • support0542 := by
  have hs : support1263 = fromList transition1227Input0 + fromList transition1227Input1 + fromList transition1227Input2 + fromList transition1227Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1227Chunk0, transition1227Chunk1, transition1227Chunk2, transition1227Chunk3]
  have hn : (transition1227Raw0 : Multiset ℕ) + (transition1227Raw1 : Multiset ℕ) + (transition1227Raw2 : Multiset ℕ) + (transition1227Raw3 : Multiset ℕ) = 1 • (supportNumbers0542 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0542] using hm

private def transition1228Input0 : List ℕ := [0, 2, 512, 514]
private def transition1228Raw0 : List ℕ := [0, 2, 256, 258]
private theorem transition1228Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1228Input0) = fromList transition1228Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1228 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0166 = 1 • support0250 := by
  have hs : support0166 = fromList transition1228Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1228Chunk0]
  have hn : (transition1228Raw0 : Multiset ℕ) = 1 • (supportNumbers0250 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0250] using hm

private def transition1229Input0 : List ℕ := [0, 2, 512, 514]
private def transition1229Raw0 : List ℕ := [0, 640, 2, 642, 256, 896, 258, 898]
private theorem transition1229Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1229Input0) = fromList transition1229Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1229 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0166 = 1 • support0251 := by
  have hs : support0166 = fromList transition1229Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1229Chunk0]
  have hn : (transition1229Raw0 : Multiset ℕ) = 1 • (supportNumbers0251 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0251] using hm

private def transition1230Input0 : List ℕ := [0, 2, 512, 514]
private def transition1230Raw0 : List ℕ := [0, 2, 256, 258]
private theorem transition1230Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1230Input0) = fromList transition1230Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1230 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0166 = 1 • support0250 := by
  have hs : support0166 = fromList transition1230Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1230Chunk0]
  have hn : (transition1230Raw0 : Multiset ℕ) = 1 • (supportNumbers0250 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0250] using hm

private def transition1231Input0 : List ℕ := [0, 2, 256, 258]
private def transition1231Raw0 : List ℕ := [0, 2]
private theorem transition1231Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1231Input0) = fromList transition1231Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1231 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0250 = 1 • support0008 := by
  have hs : support0250 = fromList transition1231Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1231Chunk0]
  have hn : (transition1231Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition1232Input0 : List ℕ := [0, 2, 256, 258]
private def transition1232Raw0 : List ℕ := [0, 578, 576, 2]
private theorem transition1232Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1232Input0) = fromList transition1232Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1232 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0250 = 1 • support0544 := by
  have hs : support0250 = fromList transition1232Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1232Chunk0]
  have hn : (transition1232Raw0 : Multiset ℕ) = 1 • (supportNumbers0544 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0544] using hm

private def transition1233Input0 : List ℕ := [0, 2, 512, 514]
private def transition1233Raw0 : List ℕ := [0, 544, 2, 546, 256, 800, 258, 802]
private theorem transition1233Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1233Input0) = fromList transition1233Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1233 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0166 = 1 • support1264 := by
  have hs : support0166 = fromList transition1233Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1233Chunk0]
  have hn : (transition1233Raw0 : Multiset ℕ) = 1 • (supportNumbers1264 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1264] using hm

private def transition1234Input0 : List ℕ := [0, 2, 256, 258, 544, 546, 800, 802]
private def transition1234Raw0 : List ℕ := [0, 2, 0, 2, 288, 290, 288, 290]
private theorem transition1234Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1234Input0) = fromList transition1234Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1234 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1264 = 2 • support0645 := by
  have hs : support1264 = fromList transition1234Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1234Chunk0]
  have hn : (transition1234Raw0 : Multiset ℕ) = 2 • (supportNumbers0645 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0645] using hm

private def transition1235Input0 : List ℕ := [0, 2, 256, 258, 544, 546, 800, 802]
private def transition1235Raw0 : List ℕ := [0, 576, 2, 578, 0, 576, 2, 578, 288, 864, 290, 866, 288, 864, 290, 866]
private theorem transition1235Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1235Input0) = fromList transition1235Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1235 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1264 = 2 • support0646 := by
  have hs : support1264 = fromList transition1235Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1235Chunk0]
  have hn : (transition1235Raw0 : Multiset ℕ) = 2 • (supportNumbers0646 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0646] using hm

private def transition1236Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition1236Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1236Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1236Input0) = fromList transition1236Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1236 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0167 = 1 • support0252 := by
  have hs : support0167 = fromList transition1236Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1236Chunk0]
  have hn : (transition1236Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1237Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition1237Raw0 : List ℕ := [0, 2, 128, 130, 640, 642, 512, 514]
private theorem transition1237Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1237Input0) = fromList transition1237Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1237 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0167 = 1 • support0253 := by
  have hs : support0167 = fromList transition1237Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1237Chunk0]
  have hn : (transition1237Raw0 : Multiset ℕ) = 1 • (supportNumbers0253 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0253] using hm

private def transition1238Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition1238Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1238Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1238Input0) = fromList transition1238Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1238 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0167 = 1 • support0252 := by
  have hs : support0167 = fromList transition1238Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1238Chunk0]
  have hn : (transition1238Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1239Input0 : List ℕ := [0, 2, 128, 130]
private def transition1239Raw0 : List ℕ := [0, 128]
private theorem transition1239Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1239Input0) = fromList transition1239Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1239 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0252 = 1 • support1265 := by
  have hs : support0252 = fromList transition1239Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1239Chunk0]
  have hn : (transition1239Raw0 : Multiset ℕ) = 1 • (supportNumbers1265 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1265] using hm

private def transition1240Input0 : List ℕ := [0, 2, 128, 130]
private def transition1240Raw0 : List ℕ := [0, 578, 128, 706]
private theorem transition1240Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1240Input0) = fromList transition1240Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1240 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0252 = 1 • support1266 := by
  have hs : support0252 = fromList transition1240Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1240Chunk0]
  have hn : (transition1240Raw0 : Multiset ℕ) = 1 • (supportNumbers1266 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1266] using hm

private def transition1241Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition1241Raw0 : List ℕ := [0, 2, 128, 130, 544, 546, 672, 674]
private theorem transition1241Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1241Input0) = fromList transition1241Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1241 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0167 = 1 • support1268 := by
  have hs : support0167 = fromList transition1241Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1241Chunk0]
  have hn : (transition1241Raw0 : Multiset ℕ) = 1 • (supportNumbers1268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1268] using hm

private def transition1242Input0 : List ℕ := [0, 2, 128, 130, 544, 546, 672, 674]
private def transition1242Raw0 : List ℕ := [0, 2, 128, 130, 288, 290, 416, 418]
private theorem transition1242Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1242Input0) = fromList transition1242Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1242 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1268 = 1 • support0799 := by
  have hs : support1268 = fromList transition1242Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1242Chunk0]
  have hn : (transition1242Raw0 : Multiset ℕ) = 1 • (supportNumbers0799 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0799] using hm

private def transition1243Input0 : List ℕ := [0, 2, 128, 130, 544, 546, 672, 674]
private def transition1243Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 288, 864, 290, 866, 416, 992, 418, 994]
private theorem transition1243Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1243Input0) = fromList transition1243Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1243 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1268 = 1 • support0800 := by
  have hs : support1268 = fromList transition1243Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1243Chunk0]
  have hn : (transition1243Raw0 : Multiset ℕ) = 1 • (supportNumbers0800 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0800] using hm

private def transition1244Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 512, 514, 640, 642, 768, 770, 896, 898]
private def transition1244Raw0 : List ℕ := [0, 2, 128, 130, 0, 2, 128, 130, 256, 258, 384, 386, 256, 258, 384, 386]
private theorem transition1244Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1244Input0) = fromList transition1244Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1244 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0168 = 2 • support0167 := by
  have hs : support0168 = fromList transition1244Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1244Chunk0]
  have hn : (transition1244Raw0 : Multiset ℕ) = 2 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition1245Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 512, 514, 640, 642, 768, 770, 896, 898]
private def transition1245Raw0 : List ℕ := [0, 640, 2, 642, 128, 512, 130, 514, 0, 640, 2, 642, 128, 512, 130, 514, 256, 896, 258, 898, 384, 768, 386, 770, 256, 896, 258, 898, 384, 768, 386, 770]
private theorem transition1245Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1245Input0) = fromList transition1245Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1245 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0168 = 2 • support0168 := by
  have hs : support0168 = fromList transition1245Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1245Chunk0]
  have hn : (transition1245Raw0 : Multiset ℕ) = 2 • (supportNumbers0168 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0168] using hm

private def transition1246Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 512, 514, 640, 642, 768, 770, 896, 898]
private def transition1246Raw0 : List ℕ := [0, 2, 128, 130, 0, 2, 128, 130, 256, 258, 384, 386, 256, 258, 384, 386]
private theorem transition1246Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1246Input0) = fromList transition1246Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1246 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0168 = 2 • support0167 := by
  have hs : support0168 = fromList transition1246Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1246Chunk0]
  have hn : (transition1246Raw0 : Multiset ℕ) = 2 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition1247Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 512, 514, 640, 642, 768, 770, 896, 898]
private def transition1247Raw0 : List ℕ := [0, 544, 2, 546, 128, 672, 130, 674, 0, 544, 2, 546, 128, 672, 130, 674, 256, 800, 258, 802, 384, 928, 386, 930, 256, 800, 258, 802, 384, 928, 386, 930]
private theorem transition1247Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1247Input0) = fromList transition1247Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1247 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0168 = 2 • support1024 := by
  have hs : support0168 = fromList transition1247Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1247Chunk0]
  have hn : (transition1247Raw0 : Multiset ℕ) = 2 • (supportNumbers1024 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1024] using hm

private def transition1248Input0 : List ℕ := [0, 2, 264, 266]
private def transition1248Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1248Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1248Input0) = fromList transition1248Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1248 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0169 = 1 • support0000 := by
  have hs : support0169 = fromList transition1248Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1248Chunk0]
  have hn : (transition1248Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1249Input0 : List ℕ := [0, 2, 264, 266]
private def transition1249Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1249Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1249Input0) = fromList transition1249Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1249 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0169 = 1 • support0000 := by
  have hs : support0169 = fromList transition1249Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1249Chunk0]
  have hn : (transition1249Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1250Input0 : List ℕ := [0, 2, 264, 266]
private def transition1250Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1250Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1250Input0) = fromList transition1250Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1250 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0169 = 1 • support0000 := by
  have hs : support0169 = fromList transition1250Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1250Chunk0]
  have hn : (transition1250Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1251Input0 : List ℕ := [0, 2, 264, 266]
private def transition1251Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1251Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1251Input0) = fromList transition1251Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1251 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0169 = 1 • support0000 := by
  have hs : support0169 = fromList transition1251Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1251Chunk0]
  have hn : (transition1251Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1252Input0 : List ℕ := [0, 2, 8, 10]
private def transition1252Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1252Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1252Input0) = fromList transition1252Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1252 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0000 = 1 • support0000 := by
  have hs : support0000 = fromList transition1252Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1252Chunk0]
  have hn : (transition1252Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1253Input0 : List ℕ := [0, 2, 8, 10]
private def transition1253Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586]
private theorem transition1253Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1253Input0) = fromList transition1253Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1253 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0000 = 1 • support1032 := by
  have hs : support0000 = fromList transition1253Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1253Chunk0]
  have hn : (transition1253Raw0 : Multiset ℕ) = 1 • (supportNumbers1032 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1032] using hm

private def transition1254Input0 : List ℕ := [0, 2, 264, 266, 640, 642, 904, 906]
private def transition1254Raw0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private theorem transition1254Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1254Input0) = fromList transition1254Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1254 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0170 = 1 • support0254 := by
  have hs : support0170 = fromList transition1254Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1254Chunk0]
  have hn : (transition1254Raw0 : Multiset ℕ) = 1 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1255Input0 : List ℕ := [0, 2, 264, 266, 640, 642, 904, 906]
private def transition1255Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition1255Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1255Input0) = fromList transition1255Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1255 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0170 = 1 • support0255 := by
  have hs : support0170 = fromList transition1255Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1255Chunk0]
  have hn : (transition1255Raw0 : Multiset ℕ) = 1 • (supportNumbers0255 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0255] using hm

private def transition1256Input0 : List ℕ := [0, 2, 264, 266, 640, 642, 904, 906]
private def transition1256Raw0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private theorem transition1256Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1256Input0) = fromList transition1256Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1256 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0170 = 1 • support0254 := by
  have hs : support0170 = fromList transition1256Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1256Chunk0]
  have hn : (transition1256Raw0 : Multiset ℕ) = 1 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1257Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1257Raw0 : List ℕ := [0, 8, 130, 138]
private theorem transition1257Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1257Input0) = fromList transition1257Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1257 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0254 = 1 • support1269 := by
  have hs : support0254 = fromList transition1257Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1257Chunk0]
  have hn : (transition1257Raw0 : Multiset ℕ) = 1 • (supportNumbers1269 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1269] using hm

private def transition1258Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394]
private def transition1258Raw0 : List ℕ := [0, 578, 8, 586, 704, 130, 712, 138]
private theorem transition1258Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1258Input0) = fromList transition1258Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1258 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0254 = 1 • support1270 := by
  have hs : support0254 = fromList transition1258Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1258Chunk0]
  have hn : (transition1258Raw0 : Multiset ℕ) = 1 • (supportNumbers1270 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1270] using hm

private def transition1259Input0 : List ℕ := [0, 2, 264, 266, 640, 642, 904, 906]
private def transition1259Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition1259Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1259Input0) = fromList transition1259Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1259 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0170 = 1 • support1272 := by
  have hs : support0170 = fromList transition1259Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1259Chunk0]
  have hn : (transition1259Raw0 : Multiset ℕ) = 1 • (supportNumbers1272 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1272] using hm

private def transition1260Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 544, 546, 552, 554, 928, 930, 936, 938]
private def transition1260Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 288, 290, 296, 298, 416, 418, 424, 426]
private theorem transition1260Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1260Input0) = fromList transition1260Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1260 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1272 = 1 • support0657 := by
  have hs : support1272 = fromList transition1260Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1260Chunk0]
  have hn : (transition1260Raw0 : Multiset ℕ) = 1 • (supportNumbers0657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0657] using hm

private def transition1261Input0 : List ℕ := [0, 2, 8, 10, 384, 386, 392, 394, 544, 546, 552, 554, 928, 930, 936, 938]
private def transition1261Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 128, 704, 130, 706, 136, 712, 138, 714, 288, 864, 290, 866, 296, 872, 298, 874, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition1261Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1261Input0) = fromList transition1261Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1261 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1272 = 1 • support0658 := by
  have hs : support1272 = fromList transition1261Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1261Chunk0]
  have hn : (transition1261Raw0 : Multiset ℕ) = 1 • (supportNumbers0658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0658] using hm

private def transition1262Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition1262Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1262Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1262Input0) = fromList transition1262Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1262 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0171 = 1 • support0000 := by
  have hs : support0171 = fromList transition1262Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1262Chunk0]
  have hn : (transition1262Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1263Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition1263Raw0 : List ℕ := [0, 2, 648, 650, 640, 642, 8, 10]
private theorem transition1263Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1263Input0) = fromList transition1263Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1263 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0171 = 1 • support0256 := by
  have hs : support0171 = fromList transition1263Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1263Chunk0]
  have hn : (transition1263Raw0 : Multiset ℕ) = 1 • (supportNumbers0256 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0256] using hm

private def transition1264Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition1264Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition1264Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1264Input0) = fromList transition1264Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1264 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0171 = 1 • support0000 := by
  have hs : support0171 = fromList transition1264Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1264Chunk0]
  have hn : (transition1264Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition1265Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition1265Raw0 : List ℕ := [0, 2, 552, 554, 544, 546, 8, 10]
private theorem transition1265Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1265Input0) = fromList transition1265Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1265 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0171 = 1 • support1273 := by
  have hs : support0171 = fromList transition1265Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1265Chunk0]
  have hn : (transition1265Raw0 : Multiset ℕ) = 1 • (supportNumbers1273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1273] using hm

private def transition1266Input0 : List ℕ := [0, 2, 8, 10, 544, 546, 552, 554]
private def transition1266Raw0 : List ℕ := [0, 2, 8, 10, 288, 290, 296, 298]
private theorem transition1266Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1266Input0) = fromList transition1266Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1266 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1273 = 1 • support1029 := by
  have hs : support1273 = fromList transition1266Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1266Chunk0]
  have hn : (transition1266Raw0 : Multiset ℕ) = 1 • (supportNumbers1029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1029] using hm

private def transition1267Input0 : List ℕ := [0, 2, 8, 10, 544, 546, 552, 554]
private def transition1267Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 288, 864, 290, 866, 296, 872, 298, 874]
private theorem transition1267Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1267Input0) = fromList transition1267Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1267 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1273 = 1 • support1030 := by
  have hs : support1273 = fromList transition1267Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1267Chunk0]
  have hn : (transition1267Raw0 : Multiset ℕ) = 1 • (supportNumbers1030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1030] using hm

private def transition1268Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 640, 642, 648, 650, 896, 898, 904, 906]
private def transition1268Raw0 : List ℕ := [0, 2, 8, 10, 0, 2, 8, 10, 384, 386, 392, 394, 384, 386, 392, 394]
private theorem transition1268Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1268Input0) = fromList transition1268Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1268 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0172 = 2 • support0254 := by
  have hs : support0172 = fromList transition1268Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1268Chunk0]
  have hn : (transition1268Raw0 : Multiset ℕ) = 2 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1269Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 640, 642, 648, 650, 896, 898, 904, 906]
private def transition1269Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 0, 640, 2, 642, 8, 648, 10, 650, 384, 768, 386, 770, 392, 776, 394, 778, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition1269Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1269Input0) = fromList transition1269Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1269 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0172 = 2 • support0255 := by
  have hs : support0172 = fromList transition1269Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1269Chunk0]
  have hn : (transition1269Raw0 : Multiset ℕ) = 2 • (supportNumbers0255 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0255] using hm

private def transition1270Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 640, 642, 648, 650, 896, 898, 904, 906]
private def transition1270Raw0 : List ℕ := [0, 2, 8, 10, 0, 2, 8, 10, 384, 386, 392, 394, 384, 386, 392, 394]
private theorem transition1270Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1270Input0) = fromList transition1270Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1270 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0172 = 2 • support0254 := by
  have hs : support0172 = fromList transition1270Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1270Chunk0]
  have hn : (transition1270Raw0 : Multiset ℕ) = 2 • (supportNumbers0254 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0254] using hm

private def transition1271Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 640, 642, 648, 650, 896, 898, 904, 906]
private def transition1271Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 0, 544, 2, 546, 8, 552, 10, 554, 384, 928, 386, 930, 392, 936, 394, 938, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition1271Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1271Input0) = fromList transition1271Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1271 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0172 = 2 • support1272 := by
  have hs : support0172 = fromList transition1271Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1271Chunk0]
  have hn : (transition1271Raw0 : Multiset ℕ) = 2 • (supportNumbers1272 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1272] using hm

private def transition1272Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition1272Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1272Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1272Input0) = fromList transition1272Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1272 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0173 = 1 • support0252 := by
  have hs : support0173 = fromList transition1272Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1272Chunk0]
  have hn : (transition1272Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1273Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition1273Raw0 : List ℕ := [0, 2, 648, 650, 128, 130, 520, 522]
private theorem transition1273Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1273Input0) = fromList transition1273Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1273 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0173 = 1 • support0257 := by
  have hs : support0173 = fromList transition1273Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1273Chunk0]
  have hn : (transition1273Raw0 : Multiset ℕ) = 1 • (supportNumbers0257 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0257] using hm

private def transition1274Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition1274Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition1274Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1274Input0) = fromList transition1274Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1274 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0173 = 1 • support0252 := by
  have hs : support0173 = fromList transition1274Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1274Chunk0]
  have hn : (transition1274Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition1275Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition1275Raw0 : List ℕ := [0, 2, 552, 554, 128, 130, 680, 682]
private theorem transition1275Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1275Input0) = fromList transition1275Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1275 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0173 = 1 • support1274 := by
  have hs : support0173 = fromList transition1275Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1275Chunk0]
  have hn : (transition1275Raw0 : Multiset ℕ) = 1 • (supportNumbers1274 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1274] using hm

private def transition1276Input0 : List ℕ := [0, 2, 128, 130, 552, 554, 680, 682]
private def transition1276Raw0 : List ℕ := [0, 2, 128, 130, 296, 298, 424, 426]
private theorem transition1276Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1276Input0) = fromList transition1276Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1276 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1274 = 1 • support1275 := by
  have hs : support1274 = fromList transition1276Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1276Chunk0]
  have hn : (transition1276Raw0 : Multiset ℕ) = 1 • (supportNumbers1275 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1275] using hm

private def transition1277Input0 : List ℕ := [0, 2, 128, 130, 552, 554, 680, 682]
private def transition1277Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 296, 872, 298, 874, 424, 1000, 426, 1002]
private theorem transition1277Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1277Input0) = fromList transition1277Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1277 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1274 = 1 • support1276 := by
  have hs : support1274 = fromList transition1277Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1277Chunk0]
  have hn : (transition1277Raw0 : Multiset ℕ) = 1 • (supportNumbers1276 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1276] using hm

private def transition1278Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 512, 514, 520, 522, 640, 642, 648, 650]
private def transition1278Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private theorem transition1278Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1278Input0) = fromList transition1278Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1278 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0174 = 1 • support0103 := by
  have hs : support0174 = fromList transition1278Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1278Chunk0]
  have hn : (transition1278Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition1279Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 512, 514, 520, 522, 640, 642, 648, 650]
private def transition1279Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 128, 512, 130, 514, 136, 520, 138, 522, 256, 896, 258, 898, 264, 904, 266, 906, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition1279Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1279Input0) = fromList transition1279Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1279 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0174 = 1 • support0104 := by
  have hs : support0174 = fromList transition1279Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1279Chunk0]
  have hn : (transition1279Raw0 : Multiset ℕ) = 1 • (supportNumbers0104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0104] using hm

private def transition1280Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 512, 514, 520, 522, 640, 642, 648, 650]
private def transition1280Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private theorem transition1280Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1280Input0) = fromList transition1280Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1280 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0174 = 1 • support0103 := by
  have hs : support0174 = fromList transition1280Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1280Chunk0]
  have hn : (transition1280Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition1281Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 512, 514, 520, 522, 640, 642, 648, 650]
private def transition1281Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 128, 672, 130, 674, 136, 680, 138, 682, 256, 800, 258, 802, 264, 808, 266, 810, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition1281Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1281Input0) = fromList transition1281Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1281 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0174 = 1 • support0816 := by
  have hs : support0174 = fromList transition1281Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1281Chunk0]
  have hn : (transition1281Raw0 : Multiset ℕ) = 1 • (supportNumbers0816 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0816] using hm

private def transition1282Input0 : List ℕ := [0, 2, 9, 11]
private def transition1282Raw0 : List ℕ := [0, 2]
private theorem transition1282Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1282Input0) = fromList transition1282Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1282 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0175 = 1 • support0008 := by
  have hs : support0175 = fromList transition1282Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1282Chunk0]
  have hn : (transition1282Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition1283Input0 : List ℕ := [0, 2, 9, 11]
private def transition1283Raw0 : List ℕ := [0, 2, 649, 651]
private theorem transition1283Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1283Input0) = fromList transition1283Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1283 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0175 = 1 • support0258 := by
  have hs : support0175 = fromList transition1283Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1283Chunk0]
  have hn : (transition1283Raw0 : Multiset ℕ) = 1 • (supportNumbers0258 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0258] using hm

private def transition1284Input0 : List ℕ := [0, 2, 9, 11]
private def transition1284Raw0 : List ℕ := [0, 2]
private theorem transition1284Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1284Input0) = fromList transition1284Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1284 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0175 = 1 • support0008 := by
  have hs : support0175 = fromList transition1284Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1284Chunk0]
  have hn : (transition1284Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition1285Input0 : List ℕ := [0, 2, 9, 11]
private def transition1285Raw0 : List ℕ := [0, 2, 553, 555]
private theorem transition1285Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1285Input0) = fromList transition1285Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1285 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0175 = 1 • support1278 := by
  have hs : support0175 = fromList transition1285Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1285Chunk0]
  have hn : (transition1285Raw0 : Multiset ℕ) = 1 • (supportNumbers1278 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1278] using hm

private def transition1286Input0 : List ℕ := [0, 2, 553, 555]
private def transition1286Raw0 : List ℕ := [0, 2, 297, 299]
private theorem transition1286Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1286Input0) = fromList transition1286Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1286 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1278 = 1 • support1279 := by
  have hs : support1278 = fromList transition1286Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1286Chunk0]
  have hn : (transition1286Raw0 : Multiset ℕ) = 1 • (supportNumbers1279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1279] using hm

private def transition1287Input0 : List ℕ := [0, 2, 553, 555]
private def transition1287Raw0 : List ℕ := [0, 576, 2, 578, 297, 873, 299, 875]
private theorem transition1287Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1287Input0) = fromList transition1287Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1287 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1278 = 1 • support1280 := by
  have hs : support1278 = fromList transition1287Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1287Chunk0]
  have hn : (transition1287Raw0 : Multiset ℕ) = 1 • (supportNumbers1280 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1280] using hm

private def transition1288Input0 : List ℕ := [0, 2, 9, 11]
private def transition1288Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition1288Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1288Input0) = fromList transition1288Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1288 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0175 = 1 • support0175 := by
  have hs : support0175 = fromList transition1288Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1288Chunk0]
  have hn : (transition1288Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
