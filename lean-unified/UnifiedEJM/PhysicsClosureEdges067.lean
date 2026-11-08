import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1153Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition1153Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879]
private theorem transition1153Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1153Input0) = fromList transition1153Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1153 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0154 = 1 • support1222 := by
  have hs : support0154 = fromList transition1153Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1153Chunk0]
  have hn : (transition1153Raw0 : Multiset ℕ) = 1 • (supportNumbers1222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1222] using hm

private def transition1154Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879]
private def transition1154Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367]
private theorem transition1154Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1154Input0) = fromList transition1154Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1154 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1222 = 1 • support1223 := by
  have hs : support1222 = fromList transition1154Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1154Chunk0]
  have hn : (transition1154Raw0 : Multiset ℕ) = 1 • (supportNumbers1223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1223] using hm

private def transition1155Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879]
private def transition1155Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815]
private theorem transition1155Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1155Input0) = fromList transition1155Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1155 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1222 = 1 • support1225 := by
  have hs : support1222 = fromList transition1155Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1155Chunk0]
  have hn : (transition1155Raw0 : Multiset ℕ) = 1 • (supportNumbers1225 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1225] using hm

private def transition1156Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1156Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1156Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1156Input0) = fromList transition1156Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1156 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0155 = 1 • support0151 := by
  have hs : support0155 = fromList transition1156Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1156Chunk0]
  have hn : (transition1156Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition1157Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1157Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 656, 657, 658, 659, 660, 661, 662, 663, 720, 721, 722, 723, 724, 725, 726, 727, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1157Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1157Input0) = fromList transition1157Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1157 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0155 = 1 • support0240 := by
  have hs : support0155 = fromList transition1157Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1157Chunk0]
  have hn : (transition1157Raw0 : Multiset ℕ) = 1 • (supportNumbers0240 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0240] using hm

private def transition1158Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1158Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1158Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1158Input0) = fromList transition1158Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1158 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0155 = 1 • support0151 := by
  have hs : support0155 = fromList transition1158Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1158Chunk0]
  have hn : (transition1158Raw0 : Multiset ℕ) = 1 • (supportNumbers0151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0151] using hm

private def transition1159Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1159Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 560, 561, 562, 563, 564, 565, 566, 567, 624, 625, 626, 627, 628, 629, 630, 631, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1159Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1159Input0) = fromList transition1159Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1159 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0155 = 1 • support1226 := by
  have hs : support0155 = fromList transition1159Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1159Chunk0]
  have hn : (transition1159Raw0 : Multiset ℕ) = 1 • (supportNumbers1226 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1226] using hm

private def transition1160Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 560, 561, 562, 563, 564, 565, 566, 567, 624, 625, 626, 627, 628, 629, 630, 631, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition1160Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition1160Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1160Input0) = fromList transition1160Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1160 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1226 = 1 • support1227 := by
  have hs : support1226 = fromList transition1160Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1160Chunk0]
  have hn : (transition1160Raw0 : Multiset ℕ) = 1 • (supportNumbers1227 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1227] using hm

private def transition1161Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 560, 561, 562, 563, 564, 565, 566, 567, 624, 625, 626, 627, 628, 629, 630, 631, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition1161Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943]
private theorem transition1161Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1161Input0) = fromList transition1161Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1161 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1226 = 1 • support1229 := by
  have hs : support1226 = fromList transition1161Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1161Chunk0]
  have hn : (transition1161Raw0 : Multiset ℕ) = 1 • (supportNumbers1229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1229] using hm

private def transition1162Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1162Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 16, 17, 18, 19, 20, 21, 22, 23, 80, 81, 82, 83, 84, 85, 86, 87, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1162Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1162Input0) = fromList transition1162Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1162Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition1162Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351, 400, 401, 402, 403, 404, 405, 406, 407, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition1162Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1162Input1) = fromList transition1162Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1162 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0156 = 1 • support0162 := by
  have hs : support0156 = fromList transition1162Input0 + fromList transition1162Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1162Chunk0, transition1162Chunk1]
  have hn : (transition1162Raw0 : Multiset ℕ) + (transition1162Raw1 : Multiset ℕ) = 1 • (supportNumbers0162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0162] using hm

private def transition1163Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition1163Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition1163Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1163Input0) = fromList transition1163Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1163Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 792, 793, 794, 795, 796, 797, 798, 799, 856, 857, 858, 859, 860, 861, 862, 863, 912, 913, 914, 915, 916, 917, 918, 919, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition1163Raw1 : List ℕ := [264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition1163Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1163Input1) = fromList transition1163Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1163 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0156 = 1 • support0163 := by
  have hs : support0156 = fromList transition1163Input0 + fromList transition1163Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1163Chunk0, transition1163Chunk1]
  have hn : (transition1163Raw0 : Multiset ℕ) + (transition1163Raw1 : Multiset ℕ) = 1 • (supportNumbers0163 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0163] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
