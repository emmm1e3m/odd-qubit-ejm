import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3026Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 560, 561, 562, 563, 564, 565, 566, 567, 624, 625, 626, 627, 628, 629, 630, 631, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private def transition3026Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition3026Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3026Input0) = fromList transition3026Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3026 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1765 = 1 • support1766 := by
  have hs : support1765 = fromList transition3026Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3026Chunk0]
  have hn : (transition3026Raw0 : Multiset ℕ) = 1 • (supportNumbers1766 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1766] using hm

private def transition3027Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 560, 561, 562, 563, 564, 565, 566, 567, 624, 625, 626, 627, 628, 629, 630, 631, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private def transition3027Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition3027Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3027Input0) = fromList transition3027Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3027 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1765 = 1 • support1768 := by
  have hs : support1765 = fromList transition3027Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3027Chunk0]
  have hn : (transition3027Raw0 : Multiset ℕ) = 1 • (supportNumbers1768 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1768] using hm

private def transition3028Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition3028Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 16, 17, 18, 19, 20, 21, 22, 23, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition3028Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3028Input0) = fromList transition3028Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3028Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3028Raw1 : List ℕ := [272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition3028Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3028Input1) = fromList transition3028Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3028 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0452 = 1 • support0414 := by
  have hs : support0452 = fromList transition3028Input0 + fromList transition3028Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3028Chunk0, transition3028Chunk1]
  have hn : (transition3028Raw0 : Multiset ℕ) + (transition3028Raw1 : Multiset ℕ) = 1 • (supportNumbers0414 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0414] using hm

private def transition3029Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition3029Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583]
private theorem transition3029Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3029Input0) = fromList transition3029Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3029Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3029Raw1 : List ℕ := [272, 912, 273, 913, 274, 914, 275, 915, 276, 916, 277, 917, 278, 918, 279, 919, 336, 976, 337, 977, 338, 978, 339, 979, 340, 980, 341, 981, 342, 982, 343, 983, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition3029Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3029Input1) = fromList transition3029Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3029 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0452 = 1 • support0415 := by
  have hs : support0452 = fromList transition3029Input0 + fromList transition3029Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3029Chunk0, transition3029Chunk1]
  have hn : (transition3029Raw0 : Multiset ℕ) + (transition3029Raw1 : Multiset ℕ) = 1 • (supportNumbers0415 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0415] using hm

private def transition3030Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition3030Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 16, 17, 18, 19, 20, 21, 22, 23, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition3030Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3030Input0) = fromList transition3030Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3030Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3030Raw1 : List ℕ := [272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition3030Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3030Input1) = fromList transition3030Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3030 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0452 = 1 • support0414 := by
  have hs : support0452 = fromList transition3030Input0 + fromList transition3030Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3030Chunk0, transition3030Chunk1]
  have hn : (transition3030Raw0 : Multiset ℕ) + (transition3030Raw1 : Multiset ℕ) = 1 • (supportNumbers0414 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0414] using hm

private def transition3031Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition3031Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743]
private theorem transition3031Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3031Input0) = fromList transition3031Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3031Input1 : List ℕ := [528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3031Raw1 : List ℕ := [272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition3031Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3031Input1) = fromList transition3031Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3031 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0452 = 1 • support1633 := by
  have hs : support0452 = fromList transition3031Input0 + fromList transition3031Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3031Chunk0, transition3031Chunk1]
  have hn : (transition3031Raw0 : Multiset ℕ) + (transition3031Raw1 : Multiset ℕ) = 1 • (supportNumbers1633 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1633] using hm

private def transition3032Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition3032Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition3032Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3032Input0) = fromList transition3032Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3032 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0453 = 1 • support0472 := by
  have hs : support0453 = fromList transition3032Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3032Chunk0]
  have hn : (transition3032Raw0 : Multiset ℕ) = 1 • (supportNumbers0472 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0472] using hm

private def transition3033Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition3033Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition3033Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3033Input0) = fromList transition3033Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3033 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0453 = 1 • support0473 := by
  have hs : support0453 = fromList transition3033Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3033Chunk0]
  have hn : (transition3033Raw0 : Multiset ℕ) = 1 • (supportNumbers0473 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0473] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
