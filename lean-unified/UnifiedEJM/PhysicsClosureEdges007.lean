import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0171Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0171Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663]
private theorem transition0171Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0171Input0) = fromList transition0171Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0171Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 632, 633, 634, 635, 636, 637, 638, 639, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition0171Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition0171Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0171Input1) = fromList transition0171Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0171 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0629 = 1 • support0632 := by
  have hs : support0629 = fromList transition0171Input0 + fromList transition0171Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0171Chunk0, transition0171Chunk1]
  have hn : (transition0171Raw0 : Multiset ℕ) + (transition0171Raw1 : Multiset ℕ) = 1 • (supportNumbers0632 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0632] using hm

private def transition0172Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0172Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0172Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0172Input0) = fromList transition0172Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0172Input1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0172Raw1 : List ℕ := [136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0172Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0172Input1) = fromList transition0172Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0172 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0022 = 1 • support0048 := by
  have hs : support0022 = fromList transition0172Input0 + fromList transition0172Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0172Chunk0, transition0172Chunk1]
  have hn : (transition0172Raw0 : Multiset ℕ) + (transition0172Raw1 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def transition0173Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0173Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 16, 17, 18, 19, 20, 21, 22, 23, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 80, 81, 82, 83, 84, 85, 86, 87, 728, 729, 730, 731, 732, 733, 734, 735]
private theorem transition0173Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0173Input0) = fromList transition0173Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0173Input1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0173Raw1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 136, 137, 138, 139, 140, 141, 142, 143, 528, 529, 530, 531, 532, 533, 534, 535, 152, 153, 154, 155, 156, 157, 158, 159, 576, 577, 578, 579, 580, 581, 582, 583, 200, 201, 202, 203, 204, 205, 206, 207, 592, 593, 594, 595, 596, 597, 598, 599, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0173Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0173Input1) = fromList transition0173Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0173 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0022 = 1 • support0049 := by
  have hs : support0022 = fromList transition0173Input0 + fromList transition0173Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0173Chunk0, transition0173Chunk1]
  have hn : (transition0173Raw0 : Multiset ℕ) + (transition0173Raw1 : Multiset ℕ) = 1 • (supportNumbers0049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0049] using hm

private def transition0174Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0174Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0174Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0174Input0) = fromList transition0174Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0174Input1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0174Raw1 : List ℕ := [136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0174Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0174Input1) = fromList transition0174Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0174 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0022 = 1 • support0048 := by
  have hs : support0022 = fromList transition0174Input0 + fromList transition0174Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0174Chunk0, transition0174Chunk1]
  have hn : (transition0174Raw0 : Multiset ℕ) + (transition0174Raw1 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def transition0175Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0175Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221]
private theorem transition0175Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0175Input0) = fromList transition0175Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0175 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0048 = 1 • support0634 := by
  have hs : support0048 = fromList transition0175Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0175Chunk0]
  have hn : (transition0175Raw0 : Multiset ℕ) = 1 • (supportNumbers0634 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0634] using hm

private def transition0176Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0176Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 16, 17, 594, 595, 20, 21, 598, 599, 64, 65, 514, 515, 68, 69, 518, 519, 80, 81, 530, 531, 84, 85, 534, 535, 136, 137, 714, 715, 140, 141, 718, 719, 152, 153, 730, 731, 156, 157, 734, 735, 200, 201, 650, 651, 204, 205, 654, 655, 216, 217, 666, 667, 220, 221, 670, 671]
private theorem transition0176Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0176Input0) = fromList transition0176Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0176 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0048 = 1 • support0636 := by
  have hs : support0048 = fromList transition0176Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0176Chunk0]
  have hn : (transition0176Raw0 : Multiset ℕ) = 1 • (supportNumbers0636 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0636] using hm

private def transition0177Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0177Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 16, 17, 18, 19, 20, 21, 22, 23, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623, 80, 81, 82, 83, 84, 85, 86, 87, 632, 633, 634, 635, 636, 637, 638, 639]
private theorem transition0177Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0177Input0) = fromList transition0177Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0177Input1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0177Raw1 : List ℕ := [672, 673, 674, 675, 676, 677, 678, 679, 136, 137, 138, 139, 140, 141, 142, 143, 688, 689, 690, 691, 692, 693, 694, 695, 152, 153, 154, 155, 156, 157, 158, 159, 736, 737, 738, 739, 740, 741, 742, 743, 200, 201, 202, 203, 204, 205, 206, 207, 752, 753, 754, 755, 756, 757, 758, 759, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0177Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0177Input1) = fromList transition0177Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0177 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0022 = 1 • support0637 := by
  have hs : support0022 = fromList transition0177Input0 + fromList transition0177Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0177Chunk0, transition0177Chunk1]
  have hn : (transition0177Raw0 : Multiset ℕ) + (transition0177Raw1 : Multiset ℕ) = 1 • (supportNumbers0637 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0637] using hm

private def transition0178Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0178Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0178Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0178Input0) = fromList transition0178Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0178Input1 : List ℕ := [552, 553, 554, 555, 556, 557, 558, 559, 568, 569, 570, 571, 572, 573, 574, 575, 616, 617, 618, 619, 620, 621, 622, 623, 632, 633, 634, 635, 636, 637, 638, 639, 672, 673, 674, 675, 676, 677, 678, 679, 688, 689, 690, 691, 692, 693, 694, 695, 736, 737, 738, 739, 740, 741, 742, 743, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition0178Raw1 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition0178Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0178Input1) = fromList transition0178Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0178 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0637 = 1 • support0638 := by
  have hs : support0637 = fromList transition0178Input0 + fromList transition0178Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0178Chunk0, transition0178Chunk1]
  have hn : (transition0178Raw0 : Multiset ℕ) + (transition0178Raw1 : Multiset ℕ) = 1 • (supportNumbers0638 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0638] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
