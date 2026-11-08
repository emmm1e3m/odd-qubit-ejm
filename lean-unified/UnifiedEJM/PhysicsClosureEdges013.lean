import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0268Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695, 808, 809, 810, 811, 820, 821, 822, 823, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition0268Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 8, 9, 10, 11, 20, 21, 22, 23, 128, 129, 130, 131, 156, 157, 158, 159, 288, 289, 290, 291, 316, 317, 318, 319, 424, 425, 426, 427, 436, 437, 438, 439, 296, 297, 298, 299, 308, 309, 310, 311, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition0268Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0268Input0) = fromList transition0268Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0268 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0701 = 1 • support0506 := by
  have hs : support0701 = fromList transition0268Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0268Chunk0]
  have hn : (transition0268Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm

private def transition0269Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695, 808, 809, 810, 811, 820, 821, 822, 823, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition0269Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0269Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0269Input0) = fromList transition0269Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0269 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0701 = 1 • support0508 := by
  have hs : support0701 = fromList transition0269Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0269Chunk0]
  have hn : (transition0269Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0270Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0270Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0270Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0270Input0) = fromList transition0270Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0270 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0034 = 1 • support0069 := by
  have hs : support0034 = fromList transition0270Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0270Chunk0]
  have hn : (transition0270Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0271Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0271Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543]
private theorem transition0271Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0271Input0) = fromList transition0271Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0271 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0034 = 1 • support0070 := by
  have hs : support0034 = fromList transition0271Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0271Chunk0]
  have hn : (transition0271Raw0 : Multiset ℕ) = 1 • (supportNumbers0070 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0070] using hm

private def transition0272Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0272Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0272Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0272Input0) = fromList transition0272Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0272 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0034 = 1 • support0069 := by
  have hs : support0034 = fromList transition0272Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0272Chunk0]
  have hn : (transition0272Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0273Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0273Raw0 : List ℕ := [0, 1, 20, 21]
private theorem transition0273Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0273Input0) = fromList transition0273Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0273 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0069 = 1 • support0702 := by
  have hs : support0069 = fromList transition0273Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0273Chunk0]
  have hn : (transition0273Raw0 : Multiset ℕ) = 1 • (supportNumbers0702 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0702] using hm

private def transition0274Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0274Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599]
private theorem transition0274Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0274Input0) = fromList transition0274Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0274 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0069 = 1 • support0703 := by
  have hs : support0069 = fromList transition0274Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0274Chunk0]
  have hn : (transition0274Raw0 : Multiset ℕ) = 1 • (supportNumbers0703 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0703] using hm

private def transition0275Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0275Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 680, 681, 682, 683, 700, 701, 702, 703]
private theorem transition0275Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0275Input0) = fromList transition0275Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0275 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0034 = 1 • support0705 := by
  have hs : support0034 = fromList transition0275Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0275Chunk0]
  have hn : (transition0275Raw0 : Multiset ℕ) = 1 • (supportNumbers0705 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0705] using hm

private def transition0276Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0276Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition0276Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0276Input0) = fromList transition0276Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0276 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0705 = 1 • support0706 := by
  have hs : support0705 = fromList transition0276Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0276Chunk0]
  have hn : (transition0276Raw0 : Multiset ℕ) = 1 • (supportNumbers0706 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0706] using hm

private def transition0277Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0277Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0277Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0277Input0) = fromList transition0277Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0277 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0705 = 1 • support0707 := by
  have hs : support0705 = fromList transition0277Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0277Chunk0]
  have hn : (transition0277Raw0 : Multiset ℕ) = 1 • (supportNumbers0707 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0707] using hm

private def transition0278Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 512, 513, 514, 515, 532, 533, 534, 535, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0278Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0278Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0278Input0) = fromList transition0278Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0278 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0035 = 1 • support0071 := by
  have hs : support0035 = fromList transition0278Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0278Chunk0]
  have hn : (transition0278Raw0 : Multiset ℕ) = 1 • (supportNumbers0071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0071] using hm

private def transition0279Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 512, 513, 514, 515, 532, 533, 534, 535, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0279Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0279Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0279Input0) = fromList transition0279Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0279 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0035 = 1 • support0072 := by
  have hs : support0035 = fromList transition0279Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0279Chunk0]
  have hn : (transition0279Raw0 : Multiset ℕ) = 1 • (supportNumbers0072 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0072] using hm

private def transition0280Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 512, 513, 514, 515, 532, 533, 534, 535, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0280Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0280Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0280Input0) = fromList transition0280Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0280 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0035 = 1 • support0071 := by
  have hs : support0035 = fromList transition0280Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0280Chunk0]
  have hn : (transition0280Raw0 : Multiset ℕ) = 1 • (supportNumbers0071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0071] using hm

private def transition0281Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0281Raw0 : List ℕ := [0, 1, 20, 21, 136, 137, 156, 157, 2, 3, 22, 23, 138, 139, 158, 159]
private theorem transition0281Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0281Input0) = fromList transition0281Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0281 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0071 = 1 • support0034 := by
  have hs : support0071 = fromList transition0281Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0281Chunk0]
  have hn : (transition0281Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition0282Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0282Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 136, 137, 714, 715, 156, 157, 734, 735, 576, 577, 2, 3, 596, 597, 22, 23, 712, 713, 138, 139, 732, 733, 158, 159]
private theorem transition0282Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0282Input0) = fromList transition0282Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0282 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0071 = 1 • support0709 := by
  have hs : support0071 = fromList transition0282Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0282Chunk0]
  have hn : (transition0282Raw0 : Multiset ℕ) = 1 • (supportNumbers0709 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0709] using hm

private def transition0283Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 512, 513, 514, 515, 532, 533, 534, 535, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0283Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0283Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0283Input0) = fromList transition0283Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0283 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0035 = 1 • support0711 := by
  have hs : support0035 = fromList transition0283Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0283Chunk0]
  have hn : (transition0283Raw0 : Multiset ℕ) = 1 • (supportNumbers0711 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0711] using hm

private def transition0284Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703, 800, 801, 802, 803, 820, 821, 822, 823, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition0284Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition0284Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0284Input0) = fromList transition0284Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0284 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0711 = 2 • support0712 := by
  have hs : support0711 = fromList transition0284Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0284Chunk0]
  have hn : (transition0284Raw0 : Multiset ℕ) = 2 • (supportNumbers0712 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0712] using hm

private def transition0285Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703, 800, 801, 802, 803, 820, 821, 822, 823, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition0285Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0285Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0285Input0) = fromList transition0285Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0285 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0711 = 2 • support0714 := by
  have hs : support0711 = fromList transition0285Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0285Chunk0]
  have hn : (transition0285Raw0 : Multiset ℕ) = 2 • (supportNumbers0714 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0714] using hm

private def transition0286Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0286Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0286Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0286Input0) = fromList transition0286Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0286 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0036 = 1 • support0073 := by
  have hs : support0036 = fromList transition0286Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0286Chunk0]
  have hn : (transition0286Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition0287Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0287Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 20, 21, 22, 23, 668, 669, 670, 671, 128, 129, 130, 131, 520, 521, 522, 523, 148, 149, 150, 151, 540, 541, 542, 543, 640, 641, 642, 643, 8, 9, 10, 11, 660, 661, 662, 663, 28, 29, 30, 31, 512, 513, 514, 515, 136, 137, 138, 139, 532, 533, 534, 535, 156, 157, 158, 159]
private theorem transition0287Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0287Input0) = fromList transition0287Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0287 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0036 = 1 • support0074 := by
  have hs : support0036 = fromList transition0287Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0287Chunk0]
  have hn : (transition0287Raw0 : Multiset ℕ) = 1 • (supportNumbers0074 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0074] using hm

private def transition0288Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0288Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0288Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0288Input0) = fromList transition0288Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0288 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0036 = 1 • support0073 := by
  have hs : support0036 = fromList transition0288Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0288Chunk0]
  have hn : (transition0288Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition0289Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0289Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 128, 129, 136, 137, 148, 149, 156, 157]
private theorem transition0289Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0289Input0) = fromList transition0289Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0289 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0073 = 1 • support0716 := by
  have hs : support0073 = fromList transition0289Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0289Chunk0]
  have hn : (transition0289Raw0 : Multiset ℕ) = 1 • (supportNumbers0716 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0716] using hm

private def transition0290Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0290Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 20, 21, 598, 599, 28, 29, 606, 607, 128, 129, 706, 707, 136, 137, 714, 715, 148, 149, 726, 727, 156, 157, 734, 735]
private theorem transition0290Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0290Input0) = fromList transition0290Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0290 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0073 = 1 • support0718 := by
  have hs : support0073 = fromList transition0290Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0290Chunk0]
  have hn : (transition0290Raw0 : Multiset ℕ) = 1 • (supportNumbers0718 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0718] using hm

private def transition0291Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0291Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 20, 21, 22, 23, 572, 573, 574, 575, 128, 129, 130, 131, 680, 681, 682, 683, 148, 149, 150, 151, 700, 701, 702, 703, 544, 545, 546, 547, 8, 9, 10, 11, 564, 565, 566, 567, 28, 29, 30, 31, 672, 673, 674, 675, 136, 137, 138, 139, 692, 693, 694, 695, 156, 157, 158, 159]
private theorem transition0291Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0291Input0) = fromList transition0291Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0291 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0036 = 1 • support0720 := by
  have hs : support0036 = fromList transition0291Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0291Chunk0]
  have hn : (transition0291Raw0 : Multiset ℕ) = 1 • (supportNumbers0720 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0720] using hm

private def transition0292Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition0292Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition0292Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0292Input0) = fromList transition0292Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0292 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0720 = 1 • support0506 := by
  have hs : support0720 = fromList transition0292Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0292Chunk0]
  have hn : (transition0292Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
