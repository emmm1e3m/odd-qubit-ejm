import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0564Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition0564Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition0564Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0564Input0) = fromList transition0564Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0564 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0072 = 2 • support0128 := by
  have hs : support0072 = fromList transition0564Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0564Chunk0]
  have hn : (transition0564Raw0 : Multiset ℕ) = 2 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0565Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0565Raw0 : List ℕ := [0, 1, 20, 21, 136, 137, 156, 157, 10, 11, 30, 31, 130, 131, 150, 151]
private theorem transition0565Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0565Input0) = fromList transition0565Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0565 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0128 = 1 • support0893 := by
  have hs : support0128 = fromList transition0565Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0565Chunk0]
  have hn : (transition0565Raw0 : Multiset ℕ) = 1 • (supportNumbers0893 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0893] using hm

private def transition0566Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0566Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 136, 137, 714, 715, 156, 157, 734, 735, 584, 585, 10, 11, 604, 605, 30, 31, 704, 705, 130, 131, 724, 725, 150, 151]
private theorem transition0566Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0566Input0) = fromList transition0566Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0566 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0128 = 1 • support0894 := by
  have hs : support0128 = fromList transition0566Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0566Chunk0]
  have hn : (transition0566Raw0 : Multiset ℕ) = 1 • (supportNumbers0894 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0894] using hm

private def transition0567Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition0567Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition0567Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0567Input0) = fromList transition0567Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0567 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0072 = 2 • support0896 := by
  have hs : support0072 = fromList transition0567Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0567Chunk0]
  have hn : (transition0567Raw0 : Multiset ℕ) = 2 • (supportNumbers0896 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0896] using hm

private def transition0568Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703, 808, 809, 810, 811, 828, 829, 830, 831, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition0568Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 8, 9, 10, 11, 28, 29, 30, 31, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447, 296, 297, 298, 299, 316, 317, 318, 319, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition0568Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0568Input0) = fromList transition0568Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0568 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0896 = 1 • support0506 := by
  have hs : support0896 = fromList transition0568Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0568Chunk0]
  have hn : (transition0568Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm

private def transition0569Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703, 808, 809, 810, 811, 828, 829, 830, 831, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition0569Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 8, 584, 9, 585, 10, 586, 11, 587, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition0569Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0569Input0) = fromList transition0569Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0569 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0896 = 1 • support0508 := by
  have hs : support0896 = fromList transition0569Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0569Chunk0]
  have hn : (transition0569Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0570Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0570Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0570Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0570Input0) = fromList transition0570Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0570 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0073 = 1 • support0130 := by
  have hs : support0073 = fromList transition0570Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0570Chunk0]
  have hn : (transition0570Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0571Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0571Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 20, 21, 22, 23, 668, 669, 670, 671, 128, 129, 130, 131, 520, 521, 522, 523, 148, 149, 150, 151, 540, 541, 542, 543]
private theorem transition0571Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0571Input0) = fromList transition0571Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0571 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0073 = 1 • support0131 := by
  have hs : support0073 = fromList transition0571Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0571Chunk0]
  have hn : (transition0571Raw0 : Multiset ℕ) = 1 • (supportNumbers0131 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0131] using hm

private def transition0572Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0572Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0572Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0572Input0) = fromList transition0572Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0572 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0073 = 1 • support0130 := by
  have hs : support0073 = fromList transition0572Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0572Chunk0]
  have hn : (transition0572Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0573Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0573Raw0 : List ℕ := [0, 1, 20, 21, 128, 129, 148, 149]
private theorem transition0573Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0573Input0) = fromList transition0573Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0573 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0130 = 1 • support0897 := by
  have hs : support0130 = fromList transition0573Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0573Chunk0]
  have hn : (transition0573Raw0 : Multiset ℕ) = 1 • (supportNumbers0897 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0897] using hm

private def transition0574Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0574Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 128, 129, 706, 707, 148, 149, 726, 727]
private theorem transition0574Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0574Input0) = fromList transition0574Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0574 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0130 = 1 • support0899 := by
  have hs : support0130 = fromList transition0574Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0574Chunk0]
  have hn : (transition0574Raw0 : Multiset ℕ) = 1 • (supportNumbers0899 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0899] using hm

private def transition0575Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0575Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 20, 21, 22, 23, 572, 573, 574, 575, 128, 129, 130, 131, 680, 681, 682, 683, 148, 149, 150, 151, 700, 701, 702, 703]
private theorem transition0575Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0575Input0) = fromList transition0575Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0575 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0073 = 1 • support0901 := by
  have hs : support0073 = fromList transition0575Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0575Chunk0]
  have hn : (transition0575Raw0 : Multiset ℕ) = 1 • (supportNumbers0901 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0901] using hm

private def transition0576Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 552, 553, 554, 555, 572, 573, 574, 575, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0576Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 296, 297, 298, 299, 316, 317, 318, 319, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition0576Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0576Input0) = fromList transition0576Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0576 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0901 = 1 • support0902 := by
  have hs : support0901 = fromList transition0576Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0576Chunk0]
  have hn : (transition0576Raw0 : Multiset ℕ) = 1 • (supportNumbers0902 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0902] using hm

private def transition0577Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 552, 553, 554, 555, 572, 573, 574, 575, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0577Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0577Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0577Input0) = fromList transition0577Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0577 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0901 = 1 • support0903 := by
  have hs : support0901 = fromList transition0577Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0577Chunk0]
  have hn : (transition0577Raw0 : Multiset ℕ) = 1 • (supportNumbers0903 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0903] using hm

private def transition0578Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0578Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0578Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0578Input0) = fromList transition0578Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0578 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0074 = 1 • support0036 := by
  have hs : support0074 = fromList transition0578Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0578Chunk0]
  have hn : (transition0578Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0579Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0579Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0579Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0579Input0) = fromList transition0579Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0579 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0074 = 1 • support0037 := by
  have hs : support0074 = fromList transition0579Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0579Chunk0]
  have hn : (transition0579Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition0580Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0580Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0580Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0580Input0) = fromList transition0580Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0580 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0074 = 1 • support0036 := by
  have hs : support0074 = fromList transition0580Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0580Chunk0]
  have hn : (transition0580Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0581Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0581Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0581Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0581Input0) = fromList transition0581Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0581 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0074 = 1 • support0593 := by
  have hs : support0074 = fromList transition0581Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0581Chunk0]
  have hn : (transition0581Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition0582Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition0582Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition0582Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0582Input0) = fromList transition0582Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0582 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0075 = 1 • support0132 := by
  have hs : support0075 = fromList transition0582Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0582Chunk0]
  have hn : (transition0582Raw0 : Multiset ℕ) = 1 • (supportNumbers0132 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0132] using hm

private def transition0583Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition0583Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition0583Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0583Input0) = fromList transition0583Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0583 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0075 = 1 • support0133 := by
  have hs : support0075 = fromList transition0583Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0583Chunk0]
  have hn : (transition0583Raw0 : Multiset ℕ) = 1 • (supportNumbers0133 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0133] using hm

private def transition0584Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition0584Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition0584Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0584Input0) = fromList transition0584Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0584 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0075 = 1 • support0132 := by
  have hs : support0075 = fromList transition0584Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0584Chunk0]
  have hn : (transition0584Raw0 : Multiset ℕ) = 1 • (supportNumbers0132 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0132] using hm

private def transition0585Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0585Raw0 : List ℕ := [0, 4, 65, 69, 130, 134, 195, 199]
private theorem transition0585Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0585Input0) = fromList transition0585Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0585 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0132 = 1 • support0905 := by
  have hs : support0132 = fromList transition0585Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0585Chunk0]
  have hn : (transition0585Raw0 : Multiset ℕ) = 1 • (supportNumbers0905 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0905] using hm

private def transition0586Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0586Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 704, 130, 708, 134, 641, 195, 645, 199]
private theorem transition0586Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0586Input0) = fromList transition0586Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0586 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0132 = 1 • support0907 := by
  have hs : support0132 = fromList transition0586Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0586Chunk0]
  have hn : (transition0586Raw0 : Multiset ℕ) = 1 • (supportNumbers0907 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0907] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
