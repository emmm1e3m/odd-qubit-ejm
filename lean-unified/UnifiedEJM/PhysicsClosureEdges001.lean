import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0047Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def transition0047Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 129, 705, 131, 707, 133, 709, 135, 711, 137, 713, 139, 715, 141, 717, 143, 719, 192, 640, 194, 642, 196, 644, 198, 646, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 296, 872, 298, 874, 300, 876, 302, 878, 353, 801, 355, 803, 357, 805, 359, 807, 361, 809, 363, 811, 365, 813, 367, 815, 417, 993, 419, 995, 421, 997, 423, 999, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 480, 928, 482, 930, 484, 932, 486, 934, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition0047Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0047Input0) = fromList transition0047Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0047 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0523 = 1 • support0526 := by
  have hs : support0523 = fromList transition0047Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0047Chunk0]
  have hn : (transition0047Raw0 : Multiset ℕ) = 1 • (supportNumbers0526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0526] using hm

private def transition0048Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0048Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0048Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0048Input0) = fromList transition0048Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0048 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0006 = 1 • support0020 := by
  have hs : support0006 = fromList transition0048Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0048Chunk0]
  have hn : (transition0048Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition0049Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0049Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 656, 657, 658, 659, 660, 661, 662, 663, 24, 25, 26, 27, 28, 29, 30, 31, 720, 721, 722, 723, 724, 725, 726, 727, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0049Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0049Input0) = fromList transition0049Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0049 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0006 = 1 • support0021 := by
  have hs : support0006 = fromList transition0049Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0049Chunk0]
  have hn : (transition0049Raw0 : Multiset ℕ) = 1 • (supportNumbers0021 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0021] using hm

private def transition0050Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0050Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0050Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0050Input0) = fromList transition0050Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0050 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0006 = 1 • support0020 := by
  have hs : support0006 = fromList transition0050Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0050Chunk0]
  have hn : (transition0050Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition0051Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0051Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93]
private theorem transition0051Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0051Input0) = fromList transition0051Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0051 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0020 = 1 • support0528 := by
  have hs : support0020 = fromList transition0051Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0051Chunk0]
  have hn : (transition0051Raw0 : Multiset ℕ) = 1 • (supportNumbers0528 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0528] using hm

private def transition0052Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0052Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 88, 89, 538, 539, 92, 93, 542, 543]
private theorem transition0052Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0052Input0) = fromList transition0052Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0052 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0020 = 1 • support0530 := by
  have hs : support0020 = fromList transition0052Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0052Chunk0]
  have hn : (transition0052Raw0 : Multiset ℕ) = 1 • (supportNumbers0530 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0530] using hm

private def transition0053Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0053Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623, 560, 561, 562, 563, 564, 565, 566, 567, 24, 25, 26, 27, 28, 29, 30, 31, 624, 625, 626, 627, 628, 629, 630, 631, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0053Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0053Input0) = fromList transition0053Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0053 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0006 = 1 • support0531 := by
  have hs : support0006 = fromList transition0053Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0053Chunk0]
  have hn : (transition0053Raw0 : Multiset ℕ) = 1 • (supportNumbers0531 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0531] using hm

private def transition0054Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631]
private def transition0054Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375]
private theorem transition0054Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0054Input0) = fromList transition0054Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0054 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0531 = 1 • support0532 := by
  have hs : support0531 = fromList transition0054Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0054Chunk0]
  have hn : (transition0054Raw0 : Multiset ℕ) = 1 • (supportNumbers0532 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0532] using hm

private def transition0055Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631]
private def transition0055Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823]
private theorem transition0055Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0055Input0) = fromList transition0055Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0055 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0531 = 1 • support0534 := by
  have hs : support0531 = fromList transition0055Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0055Chunk0]
  have hn : (transition0055Raw0 : Multiset ℕ) = 1 • (supportNumbers0534 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0534] using hm

private def transition0056Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0056Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0056Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0056Input0) = fromList transition0056Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0056Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition0056Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0056Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0056Input1) = fromList transition0056Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0056 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0007 = 1 • support0022 := by
  have hs : support0007 = fromList transition0056Input0 + fromList transition0056Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0056Chunk0, transition0056Chunk1]
  have hn : (transition0056Raw0 : Multiset ℕ) + (transition0056Raw1 : Multiset ℕ) = 1 • (supportNumbers0022 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0022] using hm

private def transition0057Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0057Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735]
private theorem transition0057Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0057Input0) = fromList transition0057Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0057Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition0057Raw1 : List ℕ := [384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition0057Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0057Input1) = fromList transition0057Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0057 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0007 = 1 • support0023 := by
  have hs : support0007 = fromList transition0057Input0 + fromList transition0057Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0057Chunk0, transition0057Chunk1]
  have hn : (transition0057Raw0 : Multiset ℕ) + (transition0057Raw1 : Multiset ℕ) = 1 • (supportNumbers0023 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0023] using hm

private def transition0058Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0058Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0058Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0058Input0) = fromList transition0058Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0058Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991]
private def transition0058Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0058Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0058Input1) = fromList transition0058Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0058 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0007 = 1 • support0022 := by
  have hs : support0007 = fromList transition0058Input0 + fromList transition0058Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0058Chunk0, transition0058Chunk1]
  have hn : (transition0058Raw0 : Multiset ℕ) + (transition0058Raw1 : Multiset ℕ) = 1 • (supportNumbers0022 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0022] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
