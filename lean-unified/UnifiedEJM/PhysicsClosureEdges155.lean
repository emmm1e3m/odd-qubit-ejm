import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2743Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2743Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition2743Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2743Input0) = fromList transition2743Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2743 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0020 = 1 • support1601 := by
  have hs : support0020 = fromList transition2743Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2743Chunk0]
  have hn : (transition2743Raw0 : Multiset ℕ) = 1 • (supportNumbers1601 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1601] using hm

private def transition2744Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2744Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2744Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2744Input0) = fromList transition2744Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2744 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0404 = 1 • support0151 := by
  have hs : support0404 = fromList transition2744Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2744Chunk0]
  have hn : (transition2744Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition2745Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2745Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 728, 729, 730, 731, 732, 733, 734, 735, 512, 513, 514, 515, 516, 517, 518, 519, 152, 153, 154, 155, 156, 157, 158, 159, 576, 577, 578, 579, 580, 581, 582, 583, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2745Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2745Input0) = fromList transition2745Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2745 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0404 = 1 • support0446 := by
  have hs : support0404 = fromList transition2745Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2745Chunk0]
  have hn : (transition2745Raw0 : Multiset ℕ) = 1 • (supportNumbers0446 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0446] using hm

private def transition2746Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2746Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2746Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2746Input0) = fromList transition2746Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2746 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0404 = 1 • support0151 := by
  have hs : support0404 = fromList transition2746Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2746Chunk0]
  have hn : (transition2746Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition2747Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2747Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 152, 153, 154, 155, 156, 157, 158, 159, 736, 737, 738, 739, 740, 741, 742, 743, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2747Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2747Input0) = fromList transition2747Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2747 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0404 = 1 • support1711 := by
  have hs : support0404 = fromList transition2747Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2747Chunk0]
  have hn : (transition2747Raw0 : Multiset ℕ) = 1 • (supportNumbers1711 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1711] using hm

private def transition2748Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private def transition2748Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition2748Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2748Input0) = fromList transition2748Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2748 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1711 = 1 • support1712 := by
  have hs : support1711 = fromList transition2748Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2748Chunk0]
  have hn : (transition2748Raw0 : Multiset ℕ) = 1 • (supportNumbers1712 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1712] using hm

private def transition2749Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private def transition2749Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition2749Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2749Input0) = fromList transition2749Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2749 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1711 = 1 • support1714 := by
  have hs : support1711 = fromList transition2749Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2749Chunk0]
  have hn : (transition2749Raw0 : Multiset ℕ) = 1 • (supportNumbers1714 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1714] using hm

private def transition2750Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2750Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2750Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2750Input0) = fromList transition2750Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2750Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735, 768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2750Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479, 256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition2750Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2750Input1) = fromList transition2750Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2750 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0405 = 1 • support0236 := by
  have hs : support0405 = fromList transition2750Input0 + fromList transition2750Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2750Chunk0, transition2750Chunk1]
  have hn : (transition2750Raw0 : Multiset ℕ) + (transition2750Raw1 : Multiset ℕ) = 1 • (supportNumbers0236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0236] using hm

private def transition2751Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2751Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition2751Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2751Input0) = fromList transition2751Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2751Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735, 768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2751Raw1 : List ℕ := [384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991]
private theorem transition2751Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2751Input1) = fromList transition2751Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2751 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0405 = 1 • support0237 := by
  have hs : support0405 = fromList transition2751Input0 + fromList transition2751Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2751Chunk0, transition2751Chunk1]
  have hn : (transition2751Raw0 : Multiset ℕ) + (transition2751Raw1 : Multiset ℕ) = 1 • (supportNumbers0237 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0237] using hm

private def transition2752Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2752Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2752Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2752Input0) = fromList transition2752Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2752Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735, 768, 769, 770, 771, 772, 773, 774, 775, 792, 793, 794, 795, 796, 797, 798, 799, 832, 833, 834, 835, 836, 837, 838, 839, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2752Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479, 256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition2752Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2752Input1) = fromList transition2752Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2752 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0405 = 1 • support0236 := by
  have hs : support0405 = fromList transition2752Input0 + fromList transition2752Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2752Chunk0, transition2752Chunk1]
  have hn : (transition2752Raw0 : Multiset ℕ) + (transition2752Raw1 : Multiset ℕ) = 1 • (supportNumbers0236 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0236] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
