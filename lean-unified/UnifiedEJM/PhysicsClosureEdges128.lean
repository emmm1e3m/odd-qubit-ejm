import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2291Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2291Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 632, 633, 634, 635, 636, 637, 638, 639, 128, 129, 130, 131, 132, 133, 134, 135, 696, 697, 698, 699, 700, 701, 702, 703, 192, 193, 194, 195, 196, 197, 198, 199, 760, 761, 762, 763, 764, 765, 766, 767]
private theorem transition2291Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2291Input0) = fromList transition2291Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2291 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0326 = 1 • support1602 := by
  have hs : support0326 = fromList transition2291Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2291Chunk0]
  have hn : (transition2291Raw0 : Multiset ℕ) = 1 • (supportNumbers1602 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1602] using hm

private def transition2292Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition2292Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition2292Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2292Input0) = fromList transition2292Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2292 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1602 = 1 • support1603 := by
  have hs : support1602 = fromList transition2292Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2292Chunk0]
  have hn : (transition2292Raw0 : Multiset ℕ) = 1 • (supportNumbers1603 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1603] using hm

private def transition2293Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 696, 697, 698, 699, 700, 701, 702, 703, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition2293Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition2293Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2293Input0) = fromList transition2293Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2293 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1602 = 1 • support1604 := by
  have hs : support1602 = fromList transition2293Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2293Chunk0]
  have hn : (transition2293Raw0 : Multiset ℕ) = 1 • (supportNumbers1604 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1604] using hm

private def transition2294Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2294Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2294Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2294Input0) = fromList transition2294Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2294Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2294Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2294Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2294Input1) = fromList transition2294Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2294 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0327 = 1 • support0236 := by
  have hs : support0327 = fromList transition2294Input0 + fromList transition2294Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2294Chunk0, transition2294Chunk1]
  have hn : (transition2294Raw0 : Multiset ℕ) + (transition2294Raw1 : Multiset ℕ) = 1 • (supportNumbers0236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0236] using hm

private def transition2295Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2295Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition2295Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2295Input0) = fromList transition2295Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2295Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2295Raw1 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition2295Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2295Input1) = fromList transition2295Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2295 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0327 = 1 • support0237 := by
  have hs : support0327 = fromList transition2295Input0 + fromList transition2295Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2295Chunk0, transition2295Chunk1]
  have hn : (transition2295Raw0 : Multiset ℕ) + (transition2295Raw1 : Multiset ℕ) = 1 • (supportNumbers0237 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0237] using hm

private def transition2296Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2296Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2296Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2296Input0) = fromList transition2296Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2296Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2296Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2296Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2296Input1) = fromList transition2296Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2296 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0327 = 1 • support0236 := by
  have hs : support0327 = fromList transition2296Input0 + fromList transition2296Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2296Chunk0, transition2296Chunk1]
  have hn : (transition2296Raw0 : Multiset ℕ) + (transition2296Raw1 : Multiset ℕ) = 1 • (supportNumbers0236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0236] using hm

private def transition2297Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition2297Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition2297Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2297Input0) = fromList transition2297Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2297Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2297Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition2297Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2297Input1) = fromList transition2297Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2297 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0327 = 1 • support1218 := by
  have hs : support0327 = fromList transition2297Input0 + fromList transition2297Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2297Chunk0, transition2297Chunk1]
  have hn : (transition2297Raw0 : Multiset ℕ) + (transition2297Raw1 : Multiset ℕ) = 1 • (supportNumbers1218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1218] using hm

private def transition2298Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition2298Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2298Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2298Input0) = fromList transition2298Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2298 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0222 = 1 • support0222 := by
  have hs : support0222 = fromList transition2298Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2298Chunk0]
  have hn : (transition2298Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition2299Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition2299Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719]
private theorem transition2299Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2299Input0) = fromList transition2299Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2299 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0222 = 1 • support0394 := by
  have hs : support0222 = fromList transition2299Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2299Chunk0]
  have hn : (transition2299Raw0 : Multiset ℕ) = 1 • (supportNumbers0394 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0394] using hm

private def transition2300Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition2300Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2300Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2300Input0) = fromList transition2300Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2300 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0222 = 1 • support0222 := by
  have hs : support0222 = fromList transition2300Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2300Chunk0]
  have hn : (transition2300Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
