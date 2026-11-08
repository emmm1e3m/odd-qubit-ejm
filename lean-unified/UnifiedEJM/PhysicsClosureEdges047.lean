import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0738Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0738Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0738Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0738Input0) = fromList transition0738Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0738Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0738Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0738Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0738Input1) = fromList transition0738Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0738Input2 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0738Raw2 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition0738Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0738Input2) = fromList transition0738Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0738Input3 : List ℕ := [776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863, 896, 897, 898, 899, 900, 901, 902, 903, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 964, 965, 966, 967, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition0738Raw3 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition0738Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0738Input3) = fromList transition0738Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0738 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0095 = 2 • support0162 := by
  have hs : support0095 = fromList transition0738Input0 + fromList transition0738Input1 + fromList transition0738Input2 + fromList transition0738Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0738Chunk0, transition0738Chunk1, transition0738Chunk2, transition0738Chunk3]
  have hn : (transition0738Raw0 : Multiset ℕ) + (transition0738Raw1 : Multiset ℕ) + (transition0738Raw2 : Multiset ℕ) + (transition0738Raw3 : Multiset ℕ) = 2 • (supportNumbers0162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0162] using hm

private def transition0739Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0739Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221]
private theorem transition0739Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0739Input0) = fromList transition0739Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0739Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0739Raw1 : List ℕ := [10, 11, 14, 15, 26, 27, 30, 31, 74, 75, 78, 79, 90, 91, 94, 95, 130, 131, 134, 135, 146, 147, 150, 151, 194, 195, 198, 199, 210, 211, 214, 215]
private theorem transition0739Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0739Input1) = fromList transition0739Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0739 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0162 = 1 • support1006 := by
  have hs : support0162 = fromList transition0739Input0 + fromList transition0739Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0739Chunk0, transition0739Chunk1]
  have hn : (transition0739Raw0 : Multiset ℕ) + (transition0739Raw1 : Multiset ℕ) = 1 • (supportNumbers1006 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1006] using hm

private def transition0740Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0740Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 16, 17, 594, 595, 20, 21, 598, 599, 64, 65, 514, 515, 68, 69, 518, 519, 80, 81, 530, 531, 84, 85, 534, 535, 136, 137, 714, 715, 140, 141, 718, 719, 152, 153, 730, 731, 156, 157, 734, 735, 200, 201, 650, 651, 204, 205, 654, 655, 216, 217, 666, 667, 220, 221, 670, 671]
private theorem transition0740Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0740Input0) = fromList transition0740Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0740Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0740Raw1 : List ℕ := [584, 585, 10, 11, 588, 589, 14, 15, 600, 601, 26, 27, 604, 605, 30, 31, 520, 521, 74, 75, 524, 525, 78, 79, 536, 537, 90, 91, 540, 541, 94, 95, 704, 705, 130, 131, 708, 709, 134, 135, 720, 721, 146, 147, 724, 725, 150, 151, 640, 641, 194, 195, 644, 645, 198, 199, 656, 657, 210, 211, 660, 661, 214, 215]
private theorem transition0740Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0740Input1) = fromList transition0740Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0740 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0162 = 1 • support1008 := by
  have hs : support0162 = fromList transition0740Input0 + fromList transition0740Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0740Chunk0, transition0740Chunk1]
  have hn : (transition0740Raw0 : Multiset ℕ) + (transition0740Raw1 : Multiset ℕ) = 1 • (supportNumbers1008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1008] using hm

private def transition0741Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0741Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0741Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0741Input0) = fromList transition0741Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0741Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0741Raw1 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0741Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0741Input1) = fromList transition0741Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0741Input2 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition0741Raw2 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition0741Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0741Input2) = fromList transition0741Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0741Input3 : List ℕ := [776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863, 896, 897, 898, 899, 900, 901, 902, 903, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 964, 965, 966, 967, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition0741Raw3 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition0741Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0741Input3) = fromList transition0741Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0741 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0095 = 2 • support1009 := by
  have hs : support0095 = fromList transition0741Input0 + fromList transition0741Input1 + fromList transition0741Input2 + fromList transition0741Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0741Chunk0, transition0741Chunk1, transition0741Chunk2, transition0741Chunk3]
  have hn : (transition0741Raw0 : Multiset ℕ) + (transition0741Raw1 : Multiset ℕ) + (transition0741Raw2 : Multiset ℕ) + (transition0741Raw3 : Multiset ℕ) = 2 • (supportNumbers1009 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1009] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
