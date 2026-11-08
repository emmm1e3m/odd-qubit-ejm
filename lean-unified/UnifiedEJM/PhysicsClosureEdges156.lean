import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2753Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2753Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition2753Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2753Input0) = fromList transition2753Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2753Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735, 768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2753Raw1 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition2753Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2753Input1) = fromList transition2753Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2753 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0405 = 1 • support1218 := by
  have hs : support0405 = fromList transition2753Input0 + fromList transition2753Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2753Chunk0, transition2753Chunk1]
  have hn : (transition2753Raw0 : Multiset ℕ) + (transition2753Raw1 : Multiset ℕ) = 1 • (supportNumbers1218 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1218] using hm

private def transition2754Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2754Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2754Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2754Input0) = fromList transition2754Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2754 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0406 = 1 • support0404 := by
  have hs : support0406 = fromList transition2754Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2754Chunk0]
  have hn : (transition2754Raw0 : Multiset ℕ) = 1 • (supportNumbers0404 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0404] using hm

private def transition2755Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2755Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition2755Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2755Input0) = fromList transition2755Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2755 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0406 = 1 • support0405 := by
  have hs : support0406 = fromList transition2755Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2755Chunk0]
  have hn : (transition2755Raw0 : Multiset ℕ) = 1 • (supportNumbers0405 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0405] using hm

private def transition2756Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2756Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2756Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2756Input0) = fromList transition2756Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2756 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0406 = 1 • support0404 := by
  have hs : support0406 = fromList transition2756Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2756Chunk0]
  have hn : (transition2756Raw0 : Multiset ℕ) = 1 • (supportNumbers0404 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0404] using hm

private def transition2757Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2757Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition2757Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2757Input0) = fromList transition2757Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2757 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0406 = 1 • support1600 := by
  have hs : support0406 = fromList transition2757Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2757Chunk0]
  have hn : (transition2757Raw0 : Multiset ℕ) = 1 • (supportNumbers1600 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1600] using hm

private def transition2758Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2758Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2758Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2758Input0) = fromList transition2758Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2758 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0407 = 1 • support0447 := by
  have hs : support0407 = fromList transition2758Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2758Chunk0]
  have hn : (transition2758Raw0 : Multiset ℕ) = 1 • (supportNumbers0447 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0447] using hm

private def transition2759Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2759Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition2759Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2759Input0) = fromList transition2759Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2759 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0407 = 1 • support0448 := by
  have hs : support0407 = fromList transition2759Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2759Chunk0]
  have hn : (transition2759Raw0 : Multiset ℕ) = 1 • (supportNumbers0448 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0448] using hm

private def transition2760Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2760Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition2760Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2760Input0) = fromList transition2760Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2760 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0407 = 1 • support0447 := by
  have hs : support0407 = fromList transition2760Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2760Chunk0]
  have hn : (transition2760Raw0 : Multiset ℕ) = 1 • (supportNumbers0447 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0447] using hm

private def transition2761Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2761Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197, 26, 27, 30, 31, 90, 91, 94, 95, 154, 155, 158, 159, 218, 219, 222, 223]
private theorem transition2761Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2761Input0) = fromList transition2761Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2761 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0447 = 1 • support1716 := by
  have hs : support0447 = fromList transition2761Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2761Chunk0]
  have hn : (transition2761Raw0 : Multiset ℕ) = 1 • (supportNumbers1716 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1716] using hm

private def transition2762Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2762Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 128, 129, 706, 707, 132, 133, 710, 711, 192, 193, 642, 643, 196, 197, 646, 647, 600, 601, 26, 27, 604, 605, 30, 31, 536, 537, 90, 91, 540, 541, 94, 95, 728, 729, 154, 155, 732, 733, 158, 159, 664, 665, 218, 219, 668, 669, 222, 223]
private theorem transition2762Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2762Input0) = fromList transition2762Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2762 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0447 = 1 • support1718 := by
  have hs : support0447 = fromList transition2762Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2762Chunk0]
  have hn : (transition2762Raw0 : Multiset ℕ) = 1 • (supportNumbers1718 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1718] using hm

private def transition2763Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition2763Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition2763Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2763Input0) = fromList transition2763Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2763 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0407 = 1 • support1719 := by
  have hs : support0407 = fromList transition2763Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2763Chunk0]
  have hn : (transition2763Raw0 : Multiset ℕ) = 1 • (supportNumbers1719 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1719] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
