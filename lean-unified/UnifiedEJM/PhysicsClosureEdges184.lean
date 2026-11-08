import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3125Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3125Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition3125Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3125Input0) = fromList transition3125Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3125 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0326 = 1 • support0327 := by
  have hs : support0326 = fromList transition3125Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3125Chunk0]
  have hn : (transition3125Raw0 : Multiset ℕ) = 1 • (supportNumbers0327 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0327] using hm

private def transition3126Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3126Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition3126Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3126Input0) = fromList transition3126Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3126 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0326 = 1 • support0326 := by
  have hs : support0326 = fromList transition3126Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3126Chunk0]
  have hn : (transition3126Raw0 : Multiset ℕ) = 1 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm

private def transition3127Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 128, 129, 130, 131, 132, 133, 134, 135, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3127Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition3127Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3127Input0) = fromList transition3127Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3127 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0326 = 1 • support1441 := by
  have hs : support0326 = fromList transition3127Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3127Chunk0]
  have hn : (transition3127Raw0 : Multiset ℕ) = 1 • (supportNumbers1441 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1441] using hm

private def transition3128Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition3128Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition3128Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3128Input0) = fromList transition3128Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3128 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0471 = 1 • support0476 := by
  have hs : support0471 = fromList transition3128Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3128Chunk0]
  have hn : (transition3128Raw0 : Multiset ℕ) = 1 • (supportNumbers0476 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0476] using hm

private def transition3129Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition3129Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition3129Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3129Input0) = fromList transition3129Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3129 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0471 = 1 • support0477 := by
  have hs : support0471 = fromList transition3129Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3129Chunk0]
  have hn : (transition3129Raw0 : Multiset ℕ) = 1 • (supportNumbers0477 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0477] using hm

private def transition3130Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition3130Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition3130Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3130Input0) = fromList transition3130Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3130 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0471 = 1 • support0476 := by
  have hs : support0471 = fromList transition3130Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3130Chunk0]
  have hn : (transition3130Raw0 : Multiset ℕ) = 1 • (supportNumbers0476 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0476] using hm

private def transition3131Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3131Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 144, 145, 148, 149, 208, 209, 212, 213, 2, 3, 6, 7, 66, 67, 70, 71, 146, 147, 150, 151, 210, 211, 214, 215]
private theorem transition3131Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3131Input0) = fromList transition3131Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3131 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0476 = 1 • support0241 := by
  have hs : support0476 = fromList transition3131Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3131Chunk0]
  have hn : (transition3131Raw0 : Multiset ℕ) = 1 • (supportNumbers0241 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0241] using hm

private def transition3132Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3132Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 144, 145, 722, 723, 148, 149, 726, 727, 208, 209, 658, 659, 212, 213, 662, 663, 576, 577, 2, 3, 580, 581, 6, 7, 512, 513, 66, 67, 516, 517, 70, 71, 720, 721, 146, 147, 724, 725, 150, 151, 656, 657, 210, 211, 660, 661, 214, 215]
private theorem transition3132Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3132Input0) = fromList transition3132Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3132 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0476 = 1 • support0471 := by
  have hs : support0476 = fromList transition3132Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3132Chunk0]
  have hn : (transition3132Raw0 : Multiset ℕ) = 1 • (supportNumbers0471 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0471] using hm

private def transition3133Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition3133Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition3133Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3133Input0) = fromList transition3133Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3133 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0471 = 1 • support1775 := by
  have hs : support0471 = fromList transition3133Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3133Chunk0]
  have hn : (transition3133Raw0 : Multiset ℕ) = 1 • (supportNumbers1775 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1775] using hm

private def transition3134Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3134Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3134Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3134Input0) = fromList transition3134Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3134Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 944, 945, 946, 947, 948, 949, 950, 951, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition3134Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition3134Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3134Input1) = fromList transition3134Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3134 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1775 = 2 • support1615 := by
  have hs : support1775 = fromList transition3134Input0 + fromList transition3134Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3134Chunk0, transition3134Chunk1]
  have hn : (transition3134Raw0 : Multiset ℕ) + (transition3134Raw1 : Multiset ℕ) = 2 • (supportNumbers1615 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1615] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
