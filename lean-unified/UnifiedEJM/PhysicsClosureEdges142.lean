import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2391Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2391Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition2391Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2391Input0) = fromList transition2391Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2391Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition2391Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition2391Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2391Input1) = fromList transition2391Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2391 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0343 = 1 • support1633 := by
  have hs : support0343 = fromList transition2391Input0 + fromList transition2391Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2391Chunk0, transition2391Chunk1]
  have hn : (transition2391Raw0 : Multiset ℕ) + (transition2391Raw1 : Multiset ℕ) = 1 • (supportNumbers1633 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1633] using hm

private def transition2392Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2392Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2392Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2392Input0) = fromList transition2392Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2392Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2392Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2392Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2392Input1) = fromList transition2392Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2392 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0096 = 1 • support0096 := by
  have hs : support0096 = fromList transition2392Input0 + fromList transition2392Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2392Chunk0, transition2392Chunk1]
  have hn : (transition2392Raw0 : Multiset ℕ) + (transition2392Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def transition2393Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2393Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735]
private theorem transition2393Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2393Input0) = fromList transition2393Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2393Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2393Raw1 : List ℕ := [128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition2393Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2393Input1) = fromList transition2393Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2393 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0096 = 1 • support0097 := by
  have hs : support0096 = fromList transition2393Input0 + fromList transition2393Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2393Chunk0, transition2393Chunk1]
  have hn : (transition2393Raw0 : Multiset ℕ) + (transition2393Raw1 : Multiset ℕ) = 1 • (supportNumbers0097 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0097] using hm

private def transition2394Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2394Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2394Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2394Input0) = fromList transition2394Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2394Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2394Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2394Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2394Input1) = fromList transition2394Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2394 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0096 = 1 • support0096 := by
  have hs : support0096 = fromList transition2394Input0 + fromList transition2394Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2394Chunk0, transition2394Chunk1]
  have hn : (transition2394Raw0 : Multiset ℕ) + (transition2394Raw1 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def transition2395Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2395Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition2395Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2395Input0) = fromList transition2395Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2395Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2395Raw1 : List ℕ := [128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition2395Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2395Input1) = fromList transition2395Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2395 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0096 = 1 • support0794 := by
  have hs : support0096 = fromList transition2395Input0 + fromList transition2395Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2395Chunk0, transition2395Chunk1]
  have hn : (transition2395Raw0 : Multiset ℕ) + (transition2395Raw1 : Multiset ℕ) = 1 • (supportNumbers0794 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0794] using hm

private def transition2396Input0 : List ℕ := [0, 2, 136, 138, 512, 514, 648, 650]
private def transition2396Raw0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private theorem transition2396Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2396Input0) = fromList transition2396Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2396 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0344 = 1 • support0418 := by
  have hs : support0344 = fromList transition2396Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2396Chunk0]
  have hn : (transition2396Raw0 : Multiset ℕ) = 1 • (supportNumbers0418 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0418] using hm

private def transition2397Input0 : List ℕ := [0, 2, 136, 138, 512, 514, 648, 650]
private def transition2397Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 256, 896, 258, 898, 392, 776, 394, 778]
private theorem transition2397Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2397Input0) = fromList transition2397Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2397 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0344 = 1 • support0419 := by
  have hs : support0344 = fromList transition2397Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2397Chunk0]
  have hn : (transition2397Raw0 : Multiset ℕ) = 1 • (supportNumbers0419 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0419] using hm

private def transition2398Input0 : List ℕ := [0, 2, 136, 138, 512, 514, 648, 650]
private def transition2398Raw0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private theorem transition2398Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2398Input0) = fromList transition2398Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2398 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0344 = 1 • support0418 := by
  have hs : support0344 = fromList transition2398Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2398Chunk0]
  have hn : (transition2398Raw0 : Multiset ℕ) = 1 • (supportNumbers0418 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0418] using hm

private def transition2399Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2399Raw0 : List ℕ := [0, 136, 2, 138]
private theorem transition2399Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2399Input0) = fromList transition2399Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2399 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0418 = 1 • support0053 := by
  have hs : support0418 = fromList transition2399Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2399Chunk0]
  have hn : (transition2399Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition2400Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2400Raw0 : List ℕ := [0, 578, 136, 714, 576, 2, 712, 138]
private theorem transition2400Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2400Input0) = fromList transition2400Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2400 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0418 = 1 • support0651 := by
  have hs : support0418 = fromList transition2400Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2400Chunk0]
  have hn : (transition2400Raw0 : Multiset ℕ) = 1 • (supportNumbers0651 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0651] using hm

private def transition2401Input0 : List ℕ := [0, 2, 136, 138, 512, 514, 648, 650]
private def transition2401Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 256, 800, 258, 802, 392, 936, 394, 938]
private theorem transition2401Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2401Input0) = fromList transition2401Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2401 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0344 = 1 • support1638 := by
  have hs : support0344 = fromList transition2401Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2401Chunk0]
  have hn : (transition2401Raw0 : Multiset ℕ) = 1 • (supportNumbers1638 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1638] using hm

private def transition2402Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 544, 546, 680, 682, 800, 802, 936, 938]
private def transition2402Raw0 : List ℕ := [0, 2, 136, 138, 0, 2, 136, 138, 288, 290, 424, 426, 288, 290, 424, 426]
private theorem transition2402Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2402Input0) = fromList transition2402Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2402 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1638 = 2 • support0550 := by
  have hs : support1638 = fromList transition2402Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2402Chunk0]
  have hn : (transition2402Raw0 : Multiset ℕ) = 2 • (supportNumbers0550 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0550] using hm

private def transition2403Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 544, 546, 680, 682, 800, 802, 936, 938]
private def transition2403Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 0, 576, 2, 578, 136, 712, 138, 714, 288, 864, 290, 866, 424, 1000, 426, 1002, 288, 864, 290, 866, 424, 1000, 426, 1002]
private theorem transition2403Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2403Input0) = fromList transition2403Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2403 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1638 = 2 • support0551 := by
  have hs : support1638 = fromList transition2403Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2403Chunk0]
  have hn : (transition2403Raw0 : Multiset ℕ) = 2 • (supportNumbers0551 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0551] using hm

private def transition2404Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition2404Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition2404Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2404Input0) = fromList transition2404Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2404 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0345 = 1 • support0173 := by
  have hs : support0345 = fromList transition2404Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2404Chunk0]
  have hn : (transition2404Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition2405Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition2405Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition2405Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2405Input0) = fromList transition2405Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2405 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0345 = 1 • support0173 := by
  have hs : support0345 = fromList transition2405Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2405Chunk0]
  have hn : (transition2405Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition2406Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition2406Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition2406Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2406Input0) = fromList transition2406Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2406 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0345 = 1 • support0173 := by
  have hs : support0345 = fromList transition2406Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2406Chunk0]
  have hn : (transition2406Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition2407Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394]
private def transition2407Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138]
private theorem transition2407Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2407Input0) = fromList transition2407Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2407 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0345 = 1 • support0173 := by
  have hs : support0345 = fromList transition2407Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2407Chunk0]
  have hn : (transition2407Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition2408Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition2408Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private theorem transition2408Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2408Input0) = fromList transition2408Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2408 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0173 = 1 • support0173 := by
  have hs : support0173 = fromList transition2408Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2408Chunk0]
  have hn : (transition2408Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition2409Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138]
private def transition2409Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 128, 704, 130, 706, 136, 712, 138, 714]
private theorem transition2409Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2409Input0) = fromList transition2409Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2409 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0173 = 1 • support0814 := by
  have hs : support0173 = fromList transition2409Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2409Chunk0]
  have hn : (transition2409Raw0 : Multiset ℕ) = 1 • (supportNumbers0814 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0814] using hm

private def transition2410Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 512, 514, 640, 642, 776, 778, 904, 906]
private def transition2410Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138, 256, 258, 384, 386, 264, 266, 392, 394]
private theorem transition2410Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2410Input0) = fromList transition2410Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2410 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0346 = 1 • support0103 := by
  have hs : support0346 = fromList transition2410Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2410Chunk0]
  have hn : (transition2410Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
