import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0398Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0398Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition0398Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0398Input0) = fromList transition0398Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0398Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0398Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0398Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0398Input1) = fromList transition0398Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0398Input2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0398Raw2 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0398Chunk2 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0398Input2) = fromList transition0398Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0398Input3 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0398Raw3 : List ℕ := [136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0398Chunk3 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0398Input3) = fromList transition0398Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0398 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0050 = 1 • support0096 := by
  have hs : support0050 = fromList transition0398Input0 + fromList transition0398Input1 + fromList transition0398Input2 + fromList transition0398Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0398Chunk0, transition0398Chunk1, transition0398Chunk2, transition0398Chunk3]
  have hn : (transition0398Raw0 : Multiset ℕ) + (transition0398Raw1 : Multiset ℕ) + (transition0398Raw2 : Multiset ℕ) + (transition0398Raw3 : Multiset ℕ) = 1 • (supportNumbers0096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0096] using hm

private def transition0399Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0399Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93]
private theorem transition0399Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0399Input0) = fromList transition0399Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0399Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0399Raw1 : List ℕ := [128, 129, 132, 133, 136, 137, 140, 141, 144, 145, 148, 149, 152, 153, 156, 157, 192, 193, 196, 197, 200, 201, 204, 205, 208, 209, 212, 213, 216, 217, 220, 221]
private theorem transition0399Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0399Input1) = fromList transition0399Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0399 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0096 = 1 • support0791 := by
  have hs : support0096 = fromList transition0399Input0 + fromList transition0399Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0399Chunk0, transition0399Chunk1]
  have hn : (transition0399Raw0 : Multiset ℕ) + (transition0399Raw1 : Multiset ℕ) = 1 • (supportNumbers0791 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0791] using hm

private def transition0400Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0400Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 8, 9, 586, 587, 12, 13, 590, 591, 16, 17, 594, 595, 20, 21, 598, 599, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 72, 73, 522, 523, 76, 77, 526, 527, 80, 81, 530, 531, 84, 85, 534, 535, 88, 89, 538, 539, 92, 93, 542, 543]
private theorem transition0400Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0400Input0) = fromList transition0400Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0400Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0400Raw1 : List ℕ := [128, 129, 706, 707, 132, 133, 710, 711, 136, 137, 714, 715, 140, 141, 718, 719, 144, 145, 722, 723, 148, 149, 726, 727, 152, 153, 730, 731, 156, 157, 734, 735, 192, 193, 642, 643, 196, 197, 646, 647, 200, 201, 650, 651, 204, 205, 654, 655, 208, 209, 658, 659, 212, 213, 662, 663, 216, 217, 666, 667, 220, 221, 670, 671]
private theorem transition0400Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0400Input1) = fromList transition0400Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0400 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0096 = 1 • support0793 := by
  have hs : support0096 = fromList transition0400Input0 + fromList transition0400Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0400Chunk0, transition0400Chunk1]
  have hn : (transition0400Raw0 : Multiset ℕ) + (transition0400Raw1 : Multiset ℕ) = 1 • (supportNumbers0793 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0793] using hm

private def transition0401Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition0401Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 16, 17, 18, 19, 20, 21, 22, 23, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623, 80, 81, 82, 83, 84, 85, 86, 87, 632, 633, 634, 635, 636, 637, 638, 639]
private theorem transition0401Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0401Input0) = fromList transition0401Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0401Input1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0401Raw1 : List ℕ := [128, 129, 130, 131, 132, 133, 134, 135, 680, 681, 682, 683, 684, 685, 686, 687, 144, 145, 146, 147, 148, 149, 150, 151, 696, 697, 698, 699, 700, 701, 702, 703, 192, 193, 194, 195, 196, 197, 198, 199, 744, 745, 746, 747, 748, 749, 750, 751, 208, 209, 210, 211, 212, 213, 214, 215, 760, 761, 762, 763, 764, 765, 766, 767]
private theorem transition0401Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0401Input1) = fromList transition0401Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0401Input2 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition0401Raw2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 8, 9, 10, 11, 12, 13, 14, 15, 560, 561, 562, 563, 564, 565, 566, 567, 24, 25, 26, 27, 28, 29, 30, 31, 608, 609, 610, 611, 612, 613, 614, 615, 72, 73, 74, 75, 76, 77, 78, 79, 624, 625, 626, 627, 628, 629, 630, 631, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition0401Chunk2 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0401Input2) = fromList transition0401Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0401Input3 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0401Raw3 : List ℕ := [672, 673, 674, 675, 676, 677, 678, 679, 136, 137, 138, 139, 140, 141, 142, 143, 688, 689, 690, 691, 692, 693, 694, 695, 152, 153, 154, 155, 156, 157, 158, 159, 736, 737, 738, 739, 740, 741, 742, 743, 200, 201, 202, 203, 204, 205, 206, 207, 752, 753, 754, 755, 756, 757, 758, 759, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0401Chunk3 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0401Input3) = fromList transition0401Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0401 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0050 = 1 • support0794 := by
  have hs : support0050 = fromList transition0401Input0 + fromList transition0401Input1 + fromList transition0401Input2 + fromList transition0401Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0401Chunk0, transition0401Chunk1, transition0401Chunk2, transition0401Chunk3]
  have hn : (transition0401Raw0 : Multiset ℕ) + (transition0401Raw1 : Multiset ℕ) + (transition0401Raw2 : Multiset ℕ) + (transition0401Raw3 : Multiset ℕ) = 1 • (supportNumbers0794 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0794] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
