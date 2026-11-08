import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1597Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1597Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654, 0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition1597Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1597Input0) = fromList transition1597Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1597Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1597Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 481, 929, 483, 931, 485, 933, 487, 935, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition1597Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1597Input1) = fromList transition1597Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1597 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1397 = 2 • support1173 := by
  have hs : support1397 = fromList transition1597Input0 + fromList transition1597Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1597Chunk0, transition1597Chunk1]
  have hn : (transition1597Raw0 : Multiset ℕ) + (transition1597Raw1 : Multiset ℕ) = 2 • (supportNumbers1173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1173] using hm

private def transition1598Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1598Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1598Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1598Input0) = fromList transition1598Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1598 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0220 = 1 • support0217 := by
  have hs : support0220 = fromList transition1598Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1598Chunk0]
  have hn : (transition1598Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1599Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1599Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591, 9, 11, 13, 15, 72, 74, 76, 78, 513, 515, 517, 519, 576, 578, 580, 582]
private theorem transition1599Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1599Input0) = fromList transition1599Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1599 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0220 = 1 • support0310 := by
  have hs : support0220 = fromList transition1599Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1599Chunk0]
  have hn : (transition1599Raw0 : Multiset ℕ) = 1 • (supportNumbers0310 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0310] using hm

private def transition1600Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1600Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 9, 11, 13, 15, 72, 74, 76, 78]
private theorem transition1600Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1600Input0) = fromList transition1600Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1600 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0220 = 1 • support0217 := by
  have hs : support0220 = fromList transition1600Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1600Chunk0]
  have hn : (transition1600Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1601Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition1601Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751, 9, 11, 13, 15, 72, 74, 76, 78, 673, 675, 677, 679, 736, 738, 740, 742]
private theorem transition1601Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1601Input0) = fromList transition1601Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1601 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0220 = 1 • support1398 := by
  have hs : support0220 = fromList transition1601Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1601Chunk0]
  have hn : (transition1601Raw0 : Multiset ℕ) = 1 • (supportNumbers1398 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1398] using hm

private def transition1602Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751]
private def transition1602Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private theorem transition1602Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1602Input0) = fromList transition1602Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1602 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1398 = 1 • support1399 := by
  have hs : support1398 = fromList transition1602Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1602Chunk0]
  have hn : (transition1602Raw0 : Multiset ℕ) = 1 • (supportNumbers1399 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1399] using hm

private def transition1603Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751]
private def transition1603Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 417, 993, 419, 995, 421, 997, 423, 999, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 480, 928, 482, 930, 484, 932, 486, 934, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition1603Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1603Input0) = fromList transition1603Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1603 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1398 = 1 • support1401 := by
  have hs : support1398 = fromList transition1603Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1603Chunk0]
  have hn : (transition1603Raw0 : Multiset ℕ) = 1 • (supportNumbers1401 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1401] using hm

private def transition1604Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1604Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 9, 11, 13, 15, 72, 74, 76, 78, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 257, 259, 261, 263, 320, 322, 324, 326, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1604Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1604Input0) = fromList transition1604Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1604 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0221 = 1 • support0227 := by
  have hs : support0221 = fromList transition1604Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1604Chunk0]
  have hn : (transition1604Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1605Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1605Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 9, 649, 11, 651, 13, 653, 15, 655, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition1605Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1605Input0) = fromList transition1605Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1605 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0221 = 1 • support0228 := by
  have hs : support0221 = fromList transition1605Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1605Chunk0]
  have hn : (transition1605Raw0 : Multiset ℕ) = 1 • (supportNumbers0228 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0228] using hm

private def transition1606Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1606Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 9, 11, 13, 15, 72, 74, 76, 78, 129, 131, 133, 135, 192, 194, 196, 198, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 257, 259, 261, 263, 320, 322, 324, 326, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition1606Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1606Input0) = fromList transition1606Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1606 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0221 = 1 • support0227 := by
  have hs : support0221 = fromList transition1606Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1606Chunk0]
  have hn : (transition1606Raw0 : Multiset ℕ) = 1 • (supportNumbers0227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0227] using hm

private def transition1607Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 385, 387, 389, 391, 448, 450, 452, 454, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition1607Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 9, 553, 11, 555, 13, 557, 15, 559, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition1607Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1607Input0) = fromList transition1607Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1607 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0221 = 1 • support1192 := by
  have hs : support0221 = fromList transition1607Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1607Chunk0]
  have hn : (transition1607Raw0 : Multiset ℕ) = 1 • (supportNumbers1192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1192] using hm

private def transition1608Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1608Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition1608Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1608Input0) = fromList transition1608Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1608 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0222 = 1 • support0044 := by
  have hs : support0222 = fromList transition1608Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1608Chunk0]
  have hn : (transition1608Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition1609Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1609Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719]
private theorem transition1609Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1609Input0) = fromList transition1609Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1609 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0222 = 1 • support0311 := by
  have hs : support0222 = fromList transition1609Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1609Chunk0]
  have hn : (transition1609Raw0 : Multiset ℕ) = 1 • (supportNumbers0311 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0311] using hm

private def transition1610Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1610Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71]
private theorem transition1610Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1610Input0) = fromList transition1610Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1610 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0222 = 1 • support0044 := by
  have hs : support0222 = fromList transition1610Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1610Chunk0]
  have hn : (transition1610Raw0 : Multiset ℕ) = 1 • (supportNumbers0044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0044] using hm

private def transition1611Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private def transition1611Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623]
private theorem transition1611Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1611Input0) = fromList transition1611Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1611 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0222 = 1 • support1402 := by
  have hs : support0222 = fromList transition1611Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1611Chunk0]
  have hn : (transition1611Raw0 : Multiset ℕ) = 1 • (supportNumbers1402 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1402] using hm

private def transition1612Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 552, 553, 554, 555, 556, 557, 558, 559, 616, 617, 618, 619, 620, 621, 622, 623]
private def transition1612Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367]
private theorem transition1612Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1612Input0) = fromList transition1612Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1612 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1402 = 1 • support1403 := by
  have hs : support1402 = fromList transition1612Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1612Chunk0]
  have hn : (transition1612Raw0 : Multiset ℕ) = 1 • (supportNumbers1403 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1403] using hm

private def transition1613Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 552, 553, 554, 555, 556, 557, 558, 559, 616, 617, 618, 619, 620, 621, 622, 623]
private def transition1613Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815]
private theorem transition1613Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1613Input0) = fromList transition1613Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1613 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1402 = 1 • support1405 := by
  have hs : support1402 = fromList transition1613Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1613Chunk0]
  have hn : (transition1613Raw0 : Multiset ℕ) = 1 • (supportNumbers1405 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1405] using hm

private def transition1614Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition1614Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private theorem transition1614Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1614Input0) = fromList transition1614Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1614 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0223 = 1 • support0312 := by
  have hs : support0223 = fromList transition1614Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1614Chunk0]
  have hn : (transition1614Raw0 : Multiset ℕ) = 1 • (supportNumbers0312 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0312] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
