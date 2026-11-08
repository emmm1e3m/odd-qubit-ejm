import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0755Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0755Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition0755Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0755Input0) = fromList transition0755Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0755Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0755Raw1 : List ℕ := [128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0755Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0755Input1) = fromList transition0755Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0755Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition0755Raw2 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition0755Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0755Input2) = fromList transition0755Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0755Input3 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0755Raw3 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0755Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0755Input3) = fromList transition0755Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0755 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0097 = 1 • support0643 := by
  have hs : support0097 = fromList transition0755Input0 + fromList transition0755Input1 + fromList transition0755Input2 + fromList transition0755Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0755Chunk0, transition0755Chunk1, transition0755Chunk2, transition0755Chunk3]
  have hn : (transition0755Raw0 : Multiset ℕ) + (transition0755Raw1 : Multiset ℕ) + (transition0755Raw2 : Multiset ℕ) + (transition0755Raw3 : Multiset ℕ) = 1 • (supportNumbers0643 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0643] using hm

private def transition0756Input0 : List ℕ := [0, 2, 384, 386]
private def transition0756Raw0 : List ℕ := [0, 2]
private theorem transition0756Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0756Input0) = fromList transition0756Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0756 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0098 = 1 • support0008 := by
  have hs : support0098 = fromList transition0756Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0756Chunk0]
  have hn : (transition0756Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0757Input0 : List ℕ := [0, 2, 384, 386]
private def transition0757Raw0 : List ℕ := [0, 2, 512, 514]
private theorem transition0757Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0757Input0) = fromList transition0757Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0757 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0098 = 1 • support0166 := by
  have hs : support0098 = fromList transition0757Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0757Chunk0]
  have hn : (transition0757Raw0 : Multiset ℕ) = 1 • (supportNumbers0166 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0166] using hm

private def transition0758Input0 : List ℕ := [0, 2, 384, 386]
private def transition0758Raw0 : List ℕ := [0, 2]
private theorem transition0758Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0758Input0) = fromList transition0758Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0758 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0098 = 1 • support0008 := by
  have hs : support0098 = fromList transition0758Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0758Chunk0]
  have hn : (transition0758Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0759Input0 : List ℕ := [0, 2, 384, 386]
private def transition0759Raw0 : List ℕ := [0, 2, 672, 674]
private theorem transition0759Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0759Input0) = fromList transition0759Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0759 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0098 = 1 • support1018 := by
  have hs : support0098 = fromList transition0759Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0759Chunk0]
  have hn : (transition0759Raw0 : Multiset ℕ) = 1 • (supportNumbers1018 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1018] using hm

private def transition0760Input0 : List ℕ := [0, 2, 672, 674]
private def transition0760Raw0 : List ℕ := [0, 2, 416, 418]
private theorem transition0760Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0760Input0) = fromList transition0760Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0760 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1018 = 1 • support1019 := by
  have hs : support1018 = fromList transition0760Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0760Chunk0]
  have hn : (transition0760Raw0 : Multiset ℕ) = 1 • (supportNumbers1019 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1019] using hm

private def transition0761Input0 : List ℕ := [0, 2, 672, 674]
private def transition0761Raw0 : List ℕ := [0, 576, 2, 578, 416, 992, 418, 994]
private theorem transition0761Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0761Input0) = fromList transition0761Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0761 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1018 = 1 • support1020 := by
  have hs : support1018 = fromList transition0761Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0761Chunk0]
  have hn : (transition0761Raw0 : Multiset ℕ) = 1 • (supportNumbers1020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1020] using hm

private def transition0762Input0 : List ℕ := [0, 2, 384, 386, 640, 642, 768, 770]
private def transition0762Raw0 : List ℕ := [0, 2, 128, 130, 384, 386, 256, 258]
private theorem transition0762Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0762Input0) = fromList transition0762Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0762 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0099 = 1 • support0167 := by
  have hs : support0099 = fromList transition0762Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0762Chunk0]
  have hn : (transition0762Raw0 : Multiset ℕ) = 1 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition0763Input0 : List ℕ := [0, 2, 384, 386, 640, 642, 768, 770]
private def transition0763Raw0 : List ℕ := [0, 640, 2, 642, 128, 512, 130, 514, 384, 768, 386, 770, 256, 896, 258, 898]
private theorem transition0763Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0763Input0) = fromList transition0763Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0763 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0099 = 1 • support0168 := by
  have hs : support0099 = fromList transition0763Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0763Chunk0]
  have hn : (transition0763Raw0 : Multiset ℕ) = 1 • (supportNumbers0168 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0168] using hm

private def transition0764Input0 : List ℕ := [0, 2, 384, 386, 640, 642, 768, 770]
private def transition0764Raw0 : List ℕ := [0, 2, 128, 130, 384, 386, 256, 258]
private theorem transition0764Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0764Input0) = fromList transition0764Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0764 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0099 = 1 • support0167 := by
  have hs : support0099 = fromList transition0764Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0764Chunk0]
  have hn : (transition0764Raw0 : Multiset ℕ) = 1 • (supportNumbers0167 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0167] using hm

private def transition0765Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition0765Raw0 : List ℕ := [0, 128, 2, 130]
private theorem transition0765Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0765Input0) = fromList transition0765Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0765 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0167 = 1 • support0252 := by
  have hs : support0167 = fromList transition0765Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0765Chunk0]
  have hn : (transition0765Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition0766Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386]
private def transition0766Raw0 : List ℕ := [0, 578, 128, 706, 576, 2, 704, 130]
private theorem transition0766Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0766Input0) = fromList transition0766Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0766 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0167 = 1 • support1022 := by
  have hs : support0167 = fromList transition0766Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0766Chunk0]
  have hn : (transition0766Raw0 : Multiset ℕ) = 1 • (supportNumbers1022 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1022] using hm

private def transition0767Input0 : List ℕ := [0, 2, 384, 386, 640, 642, 768, 770]
private def transition0767Raw0 : List ℕ := [0, 544, 2, 546, 128, 672, 130, 674, 384, 928, 386, 930, 256, 800, 258, 802]
private theorem transition0767Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0767Input0) = fromList transition0767Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0767 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0099 = 1 • support1024 := by
  have hs : support0099 = fromList transition0767Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0767Chunk0]
  have hn : (transition0767Raw0 : Multiset ℕ) = 1 • (supportNumbers1024 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1024] using hm

private def transition0768Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 544, 546, 672, 674, 800, 802, 928, 930]
private def transition0768Raw0 : List ℕ := [0, 2, 128, 130, 0, 2, 128, 130, 288, 290, 416, 418, 288, 290, 416, 418]
private theorem transition0768Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0768Input0) = fromList transition0768Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0768 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1024 = 2 • support0799 := by
  have hs : support1024 = fromList transition0768Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0768Chunk0]
  have hn : (transition0768Raw0 : Multiset ℕ) = 2 • (supportNumbers0799 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0799] using hm

private def transition0769Input0 : List ℕ := [0, 2, 128, 130, 256, 258, 384, 386, 544, 546, 672, 674, 800, 802, 928, 930]
private def transition0769Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 0, 576, 2, 578, 128, 704, 130, 706, 288, 864, 290, 866, 416, 992, 418, 994, 288, 864, 290, 866, 416, 992, 418, 994]
private theorem transition0769Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0769Input0) = fromList transition0769Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0769 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1024 = 2 • support0800 := by
  have hs : support1024 = fromList transition0769Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0769Chunk0]
  have hn : (transition0769Raw0 : Multiset ℕ) = 2 • (supportNumbers0800 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0800] using hm

private def transition0770Input0 : List ℕ := [0, 2, 520, 522]
private def transition0770Raw0 : List ℕ := [0, 2, 264, 266]
private theorem transition0770Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0770Input0) = fromList transition0770Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0770 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0100 = 1 • support0169 := by
  have hs : support0100 = fromList transition0770Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0770Chunk0]
  have hn : (transition0770Raw0 : Multiset ℕ) = 1 • (supportNumbers0169 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0169] using hm

private def transition0771Input0 : List ℕ := [0, 2, 520, 522]
private def transition0771Raw0 : List ℕ := [0, 640, 2, 642, 264, 904, 266, 906]
private theorem transition0771Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0771Input0) = fromList transition0771Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0771 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0100 = 1 • support0170 := by
  have hs : support0100 = fromList transition0771Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0771Chunk0]
  have hn : (transition0771Raw0 : Multiset ℕ) = 1 • (supportNumbers0170 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0170] using hm

private def transition0772Input0 : List ℕ := [0, 2, 520, 522]
private def transition0772Raw0 : List ℕ := [0, 2, 264, 266]
private theorem transition0772Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0772Input0) = fromList transition0772Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0772 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0100 = 1 • support0169 := by
  have hs : support0100 = fromList transition0772Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0772Chunk0]
  have hn : (transition0772Raw0 : Multiset ℕ) = 1 • (supportNumbers0169 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0169] using hm

private def transition0773Input0 : List ℕ := [0, 2, 264, 266]
private def transition0773Raw0 : List ℕ := [0, 10]
private theorem transition0773Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0773Input0) = fromList transition0773Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0773 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0169 = 1 • support1025 := by
  have hs : support0169 = fromList transition0773Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0773Chunk0]
  have hn : (transition0773Raw0 : Multiset ℕ) = 1 • (supportNumbers1025 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1025] using hm

private def transition0774Input0 : List ℕ := [0, 2, 264, 266]
private def transition0774Raw0 : List ℕ := [0, 578, 584, 10]
private theorem transition0774Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0774Input0) = fromList transition0774Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0774 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0169 = 1 • support1026 := by
  have hs : support0169 = fromList transition0774Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0774Chunk0]
  have hn : (transition0774Raw0 : Multiset ℕ) = 1 • (supportNumbers1026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1026] using hm

private def transition0775Input0 : List ℕ := [0, 2, 520, 522]
private def transition0775Raw0 : List ℕ := [0, 544, 2, 546, 264, 808, 266, 810]
private theorem transition0775Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0775Input0) = fromList transition0775Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0775 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0100 = 1 • support1028 := by
  have hs : support0100 = fromList transition0775Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0775Chunk0]
  have hn : (transition0775Raw0 : Multiset ℕ) = 1 • (supportNumbers1028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1028] using hm

private def transition0776Input0 : List ℕ := [0, 2, 264, 266, 544, 546, 808, 810]
private def transition0776Raw0 : List ℕ := [0, 2, 8, 10, 288, 290, 296, 298]
private theorem transition0776Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0776Input0) = fromList transition0776Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0776 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1028 = 1 • support1029 := by
  have hs : support1028 = fromList transition0776Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0776Chunk0]
  have hn : (transition0776Raw0 : Multiset ℕ) = 1 • (supportNumbers1029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1029] using hm

private def transition0777Input0 : List ℕ := [0, 2, 264, 266, 544, 546, 808, 810]
private def transition0777Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 288, 864, 290, 866, 296, 872, 298, 874]
private theorem transition0777Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0777Input0) = fromList transition0777Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0777 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1028 = 1 • support1030 := by
  have hs : support1028 = fromList transition0777Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0777Chunk0]
  have hn : (transition0777Raw0 : Multiset ℕ) = 1 • (supportNumbers1030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1030] using hm

private def transition0778Input0 : List ℕ := [0, 2, 136, 138, 520, 522, 640, 642]
private def transition0778Raw0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private theorem transition0778Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0778Input0) = fromList transition0778Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0778 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0101 = 1 • support0054 := by
  have hs : support0101 = fromList transition0778Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0778Chunk0]
  have hn : (transition0778Raw0 : Multiset ℕ) = 1 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition0779Input0 : List ℕ := [0, 2, 136, 138, 520, 522, 640, 642]
private def transition0779Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 264, 904, 266, 906, 384, 768, 386, 770]
private theorem transition0779Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0779Input0) = fromList transition0779Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0779 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0101 = 1 • support0055 := by
  have hs : support0101 = fromList transition0779Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0779Chunk0]
  have hn : (transition0779Raw0 : Multiset ℕ) = 1 • (supportNumbers0055 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0055] using hm

private def transition0780Input0 : List ℕ := [0, 2, 136, 138, 520, 522, 640, 642]
private def transition0780Raw0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386]
private theorem transition0780Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0780Input0) = fromList transition0780Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0780 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0101 = 1 • support0054 := by
  have hs : support0101 = fromList transition0780Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0780Chunk0]
  have hn : (transition0780Raw0 : Multiset ℕ) = 1 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition0781Input0 : List ℕ := [0, 2, 136, 138, 520, 522, 640, 642]
private def transition0781Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 264, 808, 266, 810, 384, 928, 386, 930]
private theorem transition0781Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0781Input0) = fromList transition0781Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0781 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0101 = 1 • support0656 := by
  have hs : support0101 = fromList transition0781Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0781Chunk0]
  have hn : (transition0781Raw0 : Multiset ℕ) = 1 • (supportNumbers0656 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0656] using hm

private def transition0782Input0 : List ℕ := [0, 2, 8, 10, 512, 514, 520, 522]
private def transition0782Raw0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private theorem transition0782Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0782Input0) = fromList transition0782Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0782 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0102 = 1 • support0171 := by
  have hs : support0102 = fromList transition0782Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0782Chunk0]
  have hn : (transition0782Raw0 : Multiset ℕ) = 1 • (supportNumbers0171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0171] using hm

private def transition0783Input0 : List ℕ := [0, 2, 8, 10, 512, 514, 520, 522]
private def transition0783Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 256, 896, 258, 898, 264, 904, 266, 906]
private theorem transition0783Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0783Input0) = fromList transition0783Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0783 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0102 = 1 • support0172 := by
  have hs : support0102 = fromList transition0783Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0783Chunk0]
  have hn : (transition0783Raw0 : Multiset ℕ) = 1 • (supportNumbers0172 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0172] using hm

private def transition0784Input0 : List ℕ := [0, 2, 8, 10, 512, 514, 520, 522]
private def transition0784Raw0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private theorem transition0784Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0784Input0) = fromList transition0784Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0784 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0102 = 1 • support0171 := by
  have hs : support0102 = fromList transition0784Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0784Chunk0]
  have hn : (transition0784Raw0 : Multiset ℕ) = 1 • (supportNumbers0171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0171] using hm

private def transition0785Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition0785Raw0 : List ℕ := [0, 8, 2, 10]
private theorem transition0785Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0785Input0) = fromList transition0785Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0785 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0171 = 1 • support0000 := by
  have hs : support0171 = fromList transition0785Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0785Chunk0]
  have hn : (transition0785Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition0786Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266]
private def transition0786Raw0 : List ℕ := [0, 578, 8, 586, 576, 2, 584, 10]
private theorem transition0786Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0786Input0) = fromList transition0786Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0786 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0171 = 1 • support1032 := by
  have hs : support0171 = fromList transition0786Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0786Chunk0]
  have hn : (transition0786Raw0 : Multiset ℕ) = 1 • (supportNumbers1032 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1032] using hm

private def transition0787Input0 : List ℕ := [0, 2, 8, 10, 512, 514, 520, 522]
private def transition0787Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 256, 800, 258, 802, 264, 808, 266, 810]
private theorem transition0787Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0787Input0) = fromList transition0787Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0787 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0102 = 1 • support1034 := by
  have hs : support0102 = fromList transition0787Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0787Chunk0]
  have hn : (transition0787Raw0 : Multiset ℕ) = 1 • (supportNumbers1034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1034] using hm

private def transition0788Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 544, 546, 552, 554, 800, 802, 808, 810]
private def transition0788Raw0 : List ℕ := [0, 2, 8, 10, 0, 2, 8, 10, 288, 290, 296, 298, 288, 290, 296, 298]
private theorem transition0788Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0788Input0) = fromList transition0788Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0788 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1034 = 2 • support1029 := by
  have hs : support1034 = fromList transition0788Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0788Chunk0]
  have hn : (transition0788Raw0 : Multiset ℕ) = 2 • (supportNumbers1029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1029] using hm

private def transition0789Input0 : List ℕ := [0, 2, 8, 10, 256, 258, 264, 266, 544, 546, 552, 554, 800, 802, 808, 810]
private def transition0789Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 0, 576, 2, 578, 8, 584, 10, 586, 288, 864, 290, 866, 296, 872, 298, 874, 288, 864, 290, 866, 296, 872, 298, 874]
private theorem transition0789Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0789Input0) = fromList transition0789Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0789 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1034 = 2 • support1030 := by
  have hs : support1034 = fromList transition0789Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0789Chunk0]
  have hn : (transition0789Raw0 : Multiset ℕ) = 2 • (supportNumbers1030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1030] using hm

private def transition0790Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0790Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition0790Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0790Input0) = fromList transition0790Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0790 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0103 = 1 • support0173 := by
  have hs : support0103 = fromList transition0790Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0790Chunk0]
  have hn : (transition0790Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition0791Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0791Raw0 : List ℕ := [0, 2, 648, 650, 128, 130, 520, 522, 640, 642, 8, 10, 512, 514, 136, 138]
private theorem transition0791Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0791Input0) = fromList transition0791Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0791 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0103 = 1 • support0174 := by
  have hs : support0103 = fromList transition0791Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0791Chunk0]
  have hn : (transition0791Raw0 : Multiset ℕ) = 1 • (supportNumbers0174 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0174] using hm

private def transition0792Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0792Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition0792Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0792Input0) = fromList transition0792Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0792 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0103 = 1 • support0173 := by
  have hs : support0103 = fromList transition0792Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0792Chunk0]
  have hn : (transition0792Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition0793Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition0793Raw0 : List ℕ := [0, 8, 128, 136]
private theorem transition0793Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0793Input0) = fromList transition0793Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0793 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0173 = 1 • support1035 := by
  have hs : support0173 = fromList transition0793Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0793Chunk0]
  have hn : (transition0793Raw0 : Multiset ℕ) = 1 • (supportNumbers1035 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1035] using hm

private def transition0794Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition0794Raw0 : List ℕ := [0, 578, 8, 586, 128, 706, 136, 714]
private theorem transition0794Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0794Input0) = fromList transition0794Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0794 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0173 = 1 • support1036 := by
  have hs : support0173 = fromList transition0794Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0794Chunk0]
  have hn : (transition0794Raw0 : Multiset ℕ) = 1 • (supportNumbers1036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1036] using hm

private def transition0795Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0795Raw0 : List ℕ := [0, 2, 552, 554, 128, 130, 680, 682, 544, 546, 8, 10, 672, 674, 136, 138]
private theorem transition0795Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0795Input0) = fromList transition0795Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0795 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0103 = 1 • support1038 := by
  have hs : support0103 = fromList transition0795Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0795Chunk0]
  have hn : (transition0795Raw0 : Multiset ℕ) = 1 • (supportNumbers1038 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1038] using hm

private def transition0796Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 544, 546, 552, 554, 672, 674, 680, 682]
private def transition0796Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 288, 290, 296, 298, 416, 418, 424, 426]
private theorem transition0796Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0796Input0) = fromList transition0796Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0796 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1038 = 1 • support0657 := by
  have hs : support1038 = fromList transition0796Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0796Chunk0]
  have hn : (transition0796Raw0 : Multiset ℕ) = 1 • (supportNumbers0657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0657] using hm

private def transition0797Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 544, 546, 552, 554, 672, 674, 680, 682]
private def transition0797Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 128, 704, 130, 706, 136, 712, 138, 714, 288, 864, 290, 866, 296, 872, 298, 874, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition0797Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0797Input0) = fromList transition0797Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0797 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1038 = 1 • support0658 := by
  have hs : support1038 = fromList transition0797Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0797Chunk0]
  have hn : (transition0797Raw0 : Multiset ℕ) = 1 • (supportNumbers0658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0658] using hm

private def transition0798Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 512, 514, 520, 522, 640, 642, 648, 650, 768, 770, 776, 778, 896, 898, 904, 906]
private def transition0798Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 256, 258, 264, 266, 384, 386, 392, 394]
private theorem transition0798Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0798Input0) = fromList transition0798Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0798 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0104 = 2 • support0103 := by
  have hs : support0104 = fromList transition0798Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0798Chunk0]
  have hn : (transition0798Raw0 : Multiset ℕ) = 2 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition0799Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 512, 514, 520, 522, 640, 642, 648, 650, 768, 770, 776, 778, 896, 898, 904, 906]
private def transition0799Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 128, 512, 130, 514, 136, 520, 138, 522, 0, 640, 2, 642, 8, 648, 10, 650, 128, 512, 130, 514, 136, 520, 138, 522, 256, 896, 258, 898, 264, 904, 266, 906, 384, 768, 386, 770, 392, 776, 394, 778, 256, 896, 258, 898, 264, 904, 266, 906, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition0799Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0799Input0) = fromList transition0799Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0799 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0104 = 2 • support0104 := by
  have hs : support0104 = fromList transition0799Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0799Chunk0]
  have hn : (transition0799Raw0 : Multiset ℕ) = 2 • (supportNumbers0104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0104] using hm

private def transition0800Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 512, 514, 520, 522, 640, 642, 648, 650, 768, 770, 776, 778, 896, 898, 904, 906]
private def transition0800Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 256, 258, 264, 266, 384, 386, 392, 394]
private theorem transition0800Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0800Input0) = fromList transition0800Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0800 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0104 = 2 • support0103 := by
  have hs : support0104 = fromList transition0800Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0800Chunk0]
  have hn : (transition0800Raw0 : Multiset ℕ) = 2 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition0801Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 512, 514, 520, 522, 640, 642, 648, 650, 768, 770, 776, 778, 896, 898, 904, 906]
private def transition0801Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 128, 672, 130, 674, 136, 680, 138, 682, 0, 544, 2, 546, 8, 552, 10, 554, 128, 672, 130, 674, 136, 680, 138, 682, 256, 800, 258, 802, 264, 808, 266, 810, 384, 928, 386, 930, 392, 936, 394, 938, 256, 800, 258, 802, 264, 808, 266, 810, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition0801Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0801Input0) = fromList transition0801Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0801 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0104 = 2 • support0816 := by
  have hs : support0104 = fromList transition0801Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0801Chunk0]
  have hn : (transition0801Raw0 : Multiset ℕ) = 2 • (supportNumbers0816 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0816] using hm

private def transition0802Input0 : List ℕ := [0, 2, 265, 267]
private def transition0802Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition0802Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0802Input0) = fromList transition0802Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0802 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0105 = 1 • support0175 := by
  have hs : support0105 = fromList transition0802Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0802Chunk0]
  have hn : (transition0802Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition0803Input0 : List ℕ := [0, 2, 265, 267]
private def transition0803Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition0803Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0803Input0) = fromList transition0803Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0803 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0105 = 1 • support0175 := by
  have hs : support0105 = fromList transition0803Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0803Chunk0]
  have hn : (transition0803Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition0804Input0 : List ℕ := [0, 2, 265, 267]
private def transition0804Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition0804Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0804Input0) = fromList transition0804Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0804 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0105 = 1 • support0175 := by
  have hs : support0105 = fromList transition0804Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0804Chunk0]
  have hn : (transition0804Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition0805Input0 : List ℕ := [0, 2, 9, 11]
private def transition0805Raw0 : List ℕ := [0, 9]
private theorem transition0805Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0805Input0) = fromList transition0805Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0805 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0175 = 1 • support1039 := by
  have hs : support0175 = fromList transition0805Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0805Chunk0]
  have hn : (transition0805Raw0 : Multiset ℕ) = 1 • (supportNumbers1039 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1039] using hm

private def transition0806Input0 : List ℕ := [0, 2, 9, 11]
private def transition0806Raw0 : List ℕ := [0, 578, 9, 587]
private theorem transition0806Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0806Input0) = fromList transition0806Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0806 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0175 = 1 • support1040 := by
  have hs : support0175 = fromList transition0806Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0806Chunk0]
  have hn : (transition0806Raw0 : Multiset ℕ) = 1 • (supportNumbers1040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1040] using hm

private def transition0807Input0 : List ℕ := [0, 2, 265, 267]
private def transition0807Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition0807Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0807Input0) = fromList transition0807Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0807 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0105 = 1 • support0175 := by
  have hs : support0105 = fromList transition0807Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0807Chunk0]
  have hn : (transition0807Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition0808Input0 : List ℕ := [0, 2, 9, 11]
private def transition0808Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition0808Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0808Input0) = fromList transition0808Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0808 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0175 = 1 • support0175 := by
  have hs : support0175 = fromList transition0808Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0808Chunk0]
  have hn : (transition0808Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition0809Input0 : List ℕ := [0, 2, 9, 11]
private def transition0809Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587]
private theorem transition0809Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0809Input0) = fromList transition0809Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0809 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0175 = 1 • support1042 := by
  have hs : support0175 = fromList transition0809Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0809Chunk0]
  have hn : (transition0809Raw0 : Multiset ℕ) = 1 • (supportNumbers1042 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1042] using hm

private def transition0810Input0 : List ℕ := [0, 2, 265, 267, 640, 642, 905, 907]
private def transition0810Raw0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private theorem transition0810Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0810Input0) = fromList transition0810Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0810 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0106 = 1 • support0176 := by
  have hs : support0106 = fromList transition0810Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0810Chunk0]
  have hn : (transition0810Raw0 : Multiset ℕ) = 1 • (supportNumbers0176 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0176] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
