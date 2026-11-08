import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2764Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2764Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2764Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2764Input0) = fromList transition2764Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2764Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition2764Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition2764Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2764Input1) = fromList transition2764Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2764 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1719 = 1 • support0976 := by
  have hs : support1719 = fromList transition2764Input0 + fromList transition2764Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2764Chunk0, transition2764Chunk1]
  have hn : (transition2764Raw0 : Multiset ℕ) + (transition2764Raw1 : Multiset ℕ) = 1 • (supportNumbers0976 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0976] using hm

private def transition2765Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2765Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition2765Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2765Input0) = fromList transition2765Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2765Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition2765Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition2765Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2765Input1) = fromList transition2765Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2765 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1719 = 1 • support0978 := by
  have hs : support1719 = fromList transition2765Input0 + fromList transition2765Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2765Chunk0, transition2765Chunk1]
  have hn : (transition2765Raw0 : Multiset ℕ) + (transition2765Raw1 : Multiset ℕ) = 1 • (supportNumbers0978 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0978] using hm

private def transition2766Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2766Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2766Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2766Input0) = fromList transition2766Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2766 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0408 = 1 • support0449 := by
  have hs : support0408 = fromList transition2766Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2766Chunk0]
  have hn : (transition2766Raw0 : Multiset ℕ) = 1 • (supportNumbers0449 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0449] using hm

private def transition2767Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2767Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition2767Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2767Input0) = fromList transition2767Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2767 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0408 = 1 • support0450 := by
  have hs : support0408 = fromList transition2767Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2767Chunk0]
  have hn : (transition2767Raw0 : Multiset ℕ) = 1 • (supportNumbers0450 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0450] using hm

private def transition2768Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2768Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2768Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2768Input0) = fromList transition2768Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2768 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0408 = 1 • support0449 := by
  have hs : support0408 = fromList transition2768Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2768Chunk0]
  have hn : (transition2768Raw0 : Multiset ℕ) = 1 • (supportNumbers0449 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0449] using hm

private def transition2769Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2769Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205, 2, 3, 6, 7, 66, 67, 70, 71, 138, 139, 142, 143, 202, 203, 206, 207]
private theorem transition2769Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2769Input0) = fromList transition2769Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2769 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0449 = 1 • support0088 := by
  have hs : support0449 = fromList transition2769Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2769Chunk0]
  have hn : (transition2769Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2770Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2770Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 136, 137, 714, 715, 140, 141, 718, 719, 200, 201, 650, 651, 204, 205, 654, 655, 576, 577, 2, 3, 580, 581, 6, 7, 512, 513, 66, 67, 516, 517, 70, 71, 712, 713, 138, 139, 716, 717, 142, 143, 648, 649, 202, 203, 652, 653, 206, 207]
private theorem transition2770Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2770Input0) = fromList transition2770Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2770 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0449 = 1 • support0408 := by
  have hs : support0449 = fromList transition2770Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2770Chunk0]
  have hn : (transition2770Raw0 : Multiset ℕ) = 1 • (supportNumbers0408 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0408] using hm

private def transition2771Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2771Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition2771Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2771Input0) = fromList transition2771Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2771 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0408 = 1 • support1720 := by
  have hs : support0408 = fromList transition2771Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2771Chunk0]
  have hn : (transition2771Raw0 : Multiset ℕ) = 1 • (supportNumbers1720 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1720] using hm

private def transition2772Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2772Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2772Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2772Input0) = fromList transition2772Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2772Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def transition2772Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition2772Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2772Input1) = fromList transition2772Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2772 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1720 = 2 • support0747 := by
  have hs : support1720 = fromList transition2772Input0 + fromList transition2772Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2772Chunk0, transition2772Chunk1]
  have hn : (transition2772Raw0 : Multiset ℕ) + (transition2772Raw1 : Multiset ℕ) = 2 • (supportNumbers0747 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0747] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
