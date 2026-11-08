import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3058Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343]
private def transition3058Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition3058Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3058Input0) = fromList transition3058Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3058Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727, 896, 897, 898, 899, 900, 901, 902, 903, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 964, 965, 966, 967, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3058Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition3058Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3058Input1) = fromList transition3058Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3058 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0458 = 2 • support0337 := by
  have hs : support0458 = fromList transition3058Input0 + fromList transition3058Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3058Chunk0, transition3058Chunk1]
  have hn : (transition3058Raw0 : Multiset ℕ) + (transition3058Raw1 : Multiset ℕ) = 2 • (supportNumbers0337 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0337] using hm

private def transition3059Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343]
private def transition3059Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631]
private theorem transition3059Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3059Input0) = fromList transition3059Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3059Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727, 896, 897, 898, 899, 900, 901, 902, 903, 912, 913, 914, 915, 916, 917, 918, 919, 960, 961, 962, 963, 964, 965, 966, 967, 976, 977, 978, 979, 980, 981, 982, 983]
private def transition3059Raw1 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition3059Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3059Input1) = fromList transition3059Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3059 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0458 = 2 • support1463 := by
  have hs : support0458 = fromList transition3059Input0 + fromList transition3059Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3059Chunk0, transition3059Chunk1]
  have hn : (transition3059Raw0 : Multiset ℕ) + (transition3059Raw1 : Multiset ℕ) = 2 • (supportNumbers1463 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1463] using hm

private def transition3060Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3060Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition3060Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3060Input0) = fromList transition3060Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3060 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0048 = 1 • support0048 := by
  have hs : support0048 = fromList transition3060Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3060Chunk0]
  have hn : (transition3060Raw0 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def transition3061Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3061Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition3061Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3061Input0) = fromList transition3061Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3061 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0048 = 1 • support0161 := by
  have hs : support0048 = fromList transition3061Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3061Chunk0]
  have hn : (transition3061Raw0 : Multiset ℕ) = 1 • (supportNumbers0161 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0161] using hm

private def transition3062Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3062Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition3062Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3062Input0) = fromList transition3062Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3062 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0048 = 1 • support0048 := by
  have hs : support0048 = fromList transition3062Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3062Chunk0]
  have hn : (transition3062Raw0 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def transition3063Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition3063Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition3063Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3063Input0) = fromList transition3063Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3063 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0048 = 1 • support1005 := by
  have hs : support0048 = fromList transition3063Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3063Chunk0]
  have hn : (transition3063Raw0 : Multiset ℕ) = 1 • (supportNumbers1005 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1005] using hm

private def transition3064Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition3064Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition3064Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3064Input0) = fromList transition3064Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3064 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0459 = 1 • support0117 := by
  have hs : support0459 = fromList transition3064Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3064Chunk0]
  have hn : (transition3064Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition3065Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition3065Raw0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543, 640, 641, 642, 643, 156, 157, 158, 159]
private theorem transition3065Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3065Input0) = fromList transition3065Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3065 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0459 = 1 • support0192 := by
  have hs : support0459 = fromList transition3065Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3065Chunk0]
  have hn : (transition3065Raw0 : Multiset ℕ) = 1 • (supportNumbers0192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0192] using hm

private def transition3066Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition3066Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition3066Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3066Input0) = fromList transition3066Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3066 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0459 = 1 • support0117 := by
  have hs : support0459 = fromList transition3066Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3066Chunk0]
  have hn : (transition3066Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition3067Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition3067Raw0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703, 544, 545, 546, 547, 156, 157, 158, 159]
private theorem transition3067Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3067Input0) = fromList transition3067Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3067 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0459 = 1 • support1088 := by
  have hs : support0459 = fromList transition3067Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3067Chunk0]
  have hn : (transition3067Raw0 : Multiset ℕ) = 1 • (supportNumbers1088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1088] using hm

private def transition3068Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 540, 541, 542, 543, 640, 641, 642, 643, 796, 797, 798, 799, 896, 897, 898, 899]
private def transition3068Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 284, 285, 286, 287, 384, 385, 386, 387]
private theorem transition3068Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3068Input0) = fromList transition3068Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3068 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0460 = 2 • support0118 := by
  have hs : support0460 = fromList transition3068Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3068Chunk0]
  have hn : (transition3068Raw0 : Multiset ℕ) = 2 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition3069Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 540, 541, 542, 543, 640, 641, 642, 643, 796, 797, 798, 799, 896, 897, 898, 899]
private def transition3069Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition3069Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3069Input0) = fromList transition3069Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3069 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0460 = 2 • support0119 := by
  have hs : support0460 = fromList transition3069Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3069Chunk0]
  have hn : (transition3069Raw0 : Multiset ℕ) = 2 • (supportNumbers0119 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0119] using hm

private def transition3070Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 540, 541, 542, 543, 640, 641, 642, 643, 796, 797, 798, 799, 896, 897, 898, 899]
private def transition3070Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 284, 285, 286, 287, 384, 385, 386, 387]
private theorem transition3070Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3070Input0) = fromList transition3070Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3070 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0460 = 2 • support0118 := by
  have hs : support0460 = fromList transition3070Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3070Chunk0]
  have hn : (transition3070Raw0 : Multiset ℕ) = 2 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition3071Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 540, 541, 542, 543, 640, 641, 642, 643, 796, 797, 798, 799, 896, 897, 898, 899]
private def transition3071Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition3071Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3071Input0) = fromList transition3071Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3071 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0460 = 2 • support0860 := by
  have hs : support0460 = fromList transition3071Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3071Chunk0]
  have hn : (transition3071Raw0 : Multiset ℕ) = 2 • (supportNumbers0860 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0860] using hm

private def transition3072Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition3072Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition3072Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3072Input0) = fromList transition3072Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3072 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0461 = 1 • support0123 := by
  have hs : support0461 = fromList transition3072Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3072Chunk0]
  have hn : (transition3072Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition3073Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition3073Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition3073Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3073Input0) = fromList transition3073Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3073 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0461 = 1 • support0123 := by
  have hs : support0461 = fromList transition3073Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3073Chunk0]
  have hn : (transition3073Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition3074Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition3074Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition3074Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3074Input0) = fromList transition3074Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3074 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0461 = 1 • support0123 := by
  have hs : support0461 = fromList transition3074Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3074Chunk0]
  have hn : (transition3074Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition3075Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition3075Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition3075Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3075Input0) = fromList transition3075Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3075 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0461 = 1 • support0123 := by
  have hs : support0461 = fromList transition3075Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3075Chunk0]
  have hn : (transition3075Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition3076Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition3076Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition3076Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3076Input0) = fromList transition3076Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3076 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0123 = 1 • support0123 := by
  have hs : support0123 = fromList transition3076Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3076Chunk0]
  have hn : (transition3076Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition3077Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition3077Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition3077Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3077Input0) = fromList transition3077Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3077 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0123 = 1 • support1113 := by
  have hs : support0123 = fromList transition3077Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3077Chunk0]
  have hn : (transition3077Raw0 : Multiset ℕ) = 1 • (supportNumbers1113 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1113] using hm

private def transition3078Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 532, 533, 534, 535, 640, 641, 642, 643, 796, 797, 798, 799, 904, 905, 906, 907]
private def transition3078Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159, 276, 277, 278, 279, 384, 385, 386, 387, 284, 285, 286, 287, 392, 393, 394, 395]
private theorem transition3078Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3078Input0) = fromList transition3078Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3078 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0462 = 1 • support0288 := by
  have hs : support0462 = fromList transition3078Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3078Chunk0]
  have hn : (transition3078Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
