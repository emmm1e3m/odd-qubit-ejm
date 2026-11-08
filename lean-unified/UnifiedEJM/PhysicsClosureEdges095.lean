import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1708Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1708Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1708Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1708Input0) = fromList transition1708Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1708Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 696, 697, 698, 699, 700, 701, 702, 703, 736, 737, 738, 739, 740, 741, 742, 743, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1708Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition1708Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1708Input1) = fromList transition1708Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1708 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1441 = 1 • support0976 := by
  have hs : support1441 = fromList transition1708Input0 + fromList transition1708Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1708Chunk0, transition1708Chunk1]
  have hn : (transition1708Raw0 : Multiset ℕ) + (transition1708Raw1 : Multiset ℕ) = 1 • (supportNumbers0976 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0976] using hm

private def transition1709Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1709Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition1709Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1709Input0) = fromList transition1709Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1709Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 696, 697, 698, 699, 700, 701, 702, 703, 736, 737, 738, 739, 740, 741, 742, 743, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition1709Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition1709Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1709Input1) = fromList transition1709Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1709 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1441 = 1 • support0978 := by
  have hs : support1441 = fromList transition1709Input0 + fromList transition1709Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1709Chunk0, transition1709Chunk1]
  have hn : (transition1709Raw0 : Multiset ℕ) + (transition1709Raw1 : Multiset ℕ) = 1 • (supportNumbers0978 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0978] using hm

private def transition1710Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1710Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1710Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1710Input0) = fromList transition1710Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1710Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1710Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1710Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1710Input1) = fromList transition1710Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1710Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition1710Raw2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition1710Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1710Input2) = fromList transition1710Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1710Input3 : List ℕ := [768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863, 896, 897, 898, 899, 900, 901, 902, 903, 920, 921, 922, 923, 924, 925, 926, 927, 960, 961, 962, 963, 964, 965, 966, 967, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition1710Raw3 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition1710Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1710Input3) = fromList transition1710Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1710 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0237 = 2 • support0236 := by
  have hs : support0237 = fromList transition1710Input0 + fromList transition1710Input1 + fromList transition1710Input2 + fromList transition1710Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1710Chunk0, transition1710Chunk1, transition1710Chunk2, transition1710Chunk3]
  have hn : (transition1710Raw0 : Multiset ℕ) + (transition1710Raw1 : Multiset ℕ) + (transition1710Raw2 : Multiset ℕ) + (transition1710Raw3 : Multiset ℕ) = 2 • (supportNumbers0236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0236] using hm

private def transition1711Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1711Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition1711Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1711Input0) = fromList transition1711Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1711Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1711Raw1 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition1711Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1711Input1) = fromList transition1711Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1711Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition1711Raw2 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition1711Chunk2 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1711Input2) = fromList transition1711Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1711Input3 : List ℕ := [768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863, 896, 897, 898, 899, 900, 901, 902, 903, 920, 921, 922, 923, 924, 925, 926, 927, 960, 961, 962, 963, 964, 965, 966, 967, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition1711Raw3 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition1711Chunk3 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1711Input3) = fromList transition1711Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1711 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0237 = 2 • support0237 := by
  have hs : support0237 = fromList transition1711Input0 + fromList transition1711Input1 + fromList transition1711Input2 + fromList transition1711Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1711Chunk0, transition1711Chunk1, transition1711Chunk2, transition1711Chunk3]
  have hn : (transition1711Raw0 : Multiset ℕ) + (transition1711Raw1 : Multiset ℕ) + (transition1711Raw2 : Multiset ℕ) + (transition1711Raw3 : Multiset ℕ) = 2 • (supportNumbers0237 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0237] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
