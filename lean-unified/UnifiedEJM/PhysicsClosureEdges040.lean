import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0684Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition0684Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition0684Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0684Input0) = fromList transition0684Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0684 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0087 = 1 • support0152 := by
  have hs : support0087 = fromList transition0684Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0684Chunk0]
  have hn : (transition0684Raw0 : Multiset ℕ) = 1 • (supportNumbers0152 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0152] using hm

private def transition0685Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0685Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 152, 153, 156, 157, 216, 217, 220, 221, 26, 27, 30, 31, 90, 91, 94, 95, 130, 131, 134, 135, 194, 195, 198, 199]
private theorem transition0685Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0685Input0) = fromList transition0685Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0685 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0152 = 1 • support0972 := by
  have hs : support0152 = fromList transition0685Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0685Chunk0]
  have hn : (transition0685Raw0 : Multiset ℕ) = 1 • (supportNumbers0972 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0972] using hm

private def transition0686Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0686Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 152, 153, 730, 731, 156, 157, 734, 735, 216, 217, 666, 667, 220, 221, 670, 671, 600, 601, 26, 27, 604, 605, 30, 31, 536, 537, 90, 91, 540, 541, 94, 95, 704, 705, 130, 131, 708, 709, 134, 135, 640, 641, 194, 195, 644, 645, 198, 199]
private theorem transition0686Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0686Input0) = fromList transition0686Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0686 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0152 = 1 • support0974 := by
  have hs : support0152 = fromList transition0686Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0686Chunk0]
  have hn : (transition0686Raw0 : Multiset ℕ) = 1 • (supportNumbers0974 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0974] using hm

private def transition0687Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition0687Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition0687Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0687Input0) = fromList transition0687Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0687 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0087 = 1 • support0975 := by
  have hs : support0087 = fromList transition0687Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0687Chunk0]
  have hn : (transition0687Raw0 : Multiset ℕ) = 1 • (supportNumbers0975 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0975] using hm

private def transition0688Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0688Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition0688Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0688Input0) = fromList transition0688Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0688Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition0688Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition0688Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0688Input1) = fromList transition0688Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0688 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0975 = 1 • support0976 := by
  have hs : support0975 = fromList transition0688Input0 + fromList transition0688Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0688Chunk0, transition0688Chunk1]
  have hn : (transition0688Raw0 : Multiset ℕ) + (transition0688Raw1 : Multiset ℕ) = 1 • (supportNumbers0976 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0976] using hm

private def transition0689Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0689Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647]
private theorem transition0689Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0689Input0) = fromList transition0689Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0689Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767, 824, 825, 826, 827, 828, 829, 830, 831, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition0689Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition0689Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0689Input1) = fromList transition0689Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0689 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0975 = 1 • support0978 := by
  have hs : support0975 = fromList transition0689Input0 + fromList transition0689Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0689Chunk0, transition0689Chunk1]
  have hn : (transition0689Raw0 : Multiset ℕ) + (transition0689Raw1 : Multiset ℕ) = 1 • (supportNumbers0978 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0978] using hm

private def transition0690Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0690Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition0690Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0690Input0) = fromList transition0690Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0690 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0088 = 1 • support0044 := by
  have hs : support0088 = fromList transition0690Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0690Chunk0]
  have hn : (transition0690Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition0691Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0691Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591]
private theorem transition0691Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0691Input0) = fromList transition0691Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0691 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0088 = 1 • support0154 := by
  have hs : support0088 = fromList transition0691Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0691Chunk0]
  have hn : (transition0691Raw0 : Multiset ℕ) = 1 • (supportNumbers0154 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0154] using hm

private def transition0692Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0692Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition0692Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0692Input0) = fromList transition0692Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0692 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0088 = 1 • support0044 := by
  have hs : support0088 = fromList transition0692Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0692Chunk0]
  have hn : (transition0692Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition0693Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0693Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private theorem transition0693Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0693Input0) = fromList transition0693Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0693 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0088 = 1 • support0980 := by
  have hs : support0088 = fromList transition0693Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0693Chunk0]
  have hn : (transition0693Raw0 : Multiset ℕ) = 1 • (supportNumbers0980 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0980] using hm

private def transition0694Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition0694Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition0694Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0694Input0) = fromList transition0694Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0694 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0980 = 1 • support0981 := by
  have hs : support0980 = fromList transition0694Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0694Chunk0]
  have hn : (transition0694Raw0 : Multiset ℕ) = 1 • (supportNumbers0981 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0981] using hm

private def transition0695Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition0695Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943]
private theorem transition0695Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0695Input0) = fromList transition0695Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0695 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0980 = 1 • support0983 := by
  have hs : support0980 = fromList transition0695Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0695Chunk0]
  have hn : (transition0695Raw0 : Multiset ℕ) = 1 • (supportNumbers0983 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0983] using hm

private def transition0696Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0696Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0696Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0696Input0) = fromList transition0696Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0696 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0089 = 1 • support0155 := by
  have hs : support0089 = fromList transition0696Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0696Chunk0]
  have hn : (transition0696Raw0 : Multiset ℕ) = 1 • (supportNumbers0155 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0155] using hm

private def transition0697Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0697Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 272, 912, 273, 913, 274, 914, 275, 915, 276, 916, 277, 917, 278, 918, 279, 919, 336, 976, 337, 977, 338, 978, 339, 979, 340, 980, 341, 981, 342, 982, 343, 983, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition0697Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0697Input0) = fromList transition0697Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0697 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0089 = 1 • support0156 := by
  have hs : support0089 = fromList transition0697Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0697Chunk0]
  have hn : (transition0697Raw0 : Multiset ℕ) = 1 • (supportNumbers0156 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0156] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
