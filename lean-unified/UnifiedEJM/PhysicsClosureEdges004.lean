import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0112Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0112Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0112Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0112Input0) = fromList transition0112Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0112 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0014 = 1 • support0034 := by
  have hs : support0014 = fromList transition0112Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0112Chunk0]
  have hn : (transition0112Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition0113Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0113Raw0 : List ℕ := [0, 1, 20, 21, 136, 137, 156, 157]
private theorem transition0113Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0113Input0) = fromList transition0113Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0113 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0034 = 1 • support0583 := by
  have hs : support0034 = fromList transition0113Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0113Chunk0]
  have hn : (transition0113Raw0 : Multiset ℕ) = 1 • (supportNumbers0583 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0583] using hm

private def transition0114Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition0114Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 136, 137, 714, 715, 156, 157, 734, 735]
private theorem transition0114Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0114Input0) = fromList transition0114Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0114 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0034 = 1 • support0585 := by
  have hs : support0034 = fromList transition0114Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0114Chunk0]
  have hn : (transition0114Raw0 : Multiset ℕ) = 1 • (supportNumbers0585 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0585] using hm

private def transition0115Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0115Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 20, 21, 22, 23, 572, 573, 574, 575, 672, 673, 674, 675, 136, 137, 138, 139, 692, 693, 694, 695, 156, 157, 158, 159]
private theorem transition0115Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0115Input0) = fromList transition0115Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0115 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0014 = 1 • support0587 := by
  have hs : support0014 = fromList transition0115Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0115Chunk0]
  have hn : (transition0115Raw0 : Multiset ℕ) = 1 • (supportNumbers0587 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0587] using hm

private def transition0116Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 552, 553, 554, 555, 572, 573, 574, 575, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition0116Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 296, 297, 298, 299, 316, 317, 318, 319, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition0116Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0116Input0) = fromList transition0116Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0116 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0587 = 1 • support0588 := by
  have hs : support0587 = fromList transition0116Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0116Chunk0]
  have hn : (transition0116Raw0 : Multiset ℕ) = 1 • (supportNumbers0588 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0588] using hm

private def transition0117Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 552, 553, 554, 555, 572, 573, 574, 575, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition0117Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition0117Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0117Input0) = fromList transition0117Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0117 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0587 = 1 • support0589 := by
  have hs : support0587 = fromList transition0117Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0117Chunk0]
  have hn : (transition0117Raw0 : Multiset ℕ) = 1 • (supportNumbers0589 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0589] using hm

private def transition0118Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799]
private def transition0118Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition0118Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0118Input0) = fromList transition0118Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0118 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0015 = 1 • support0036 := by
  have hs : support0015 = fromList transition0118Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0118Chunk0]
  have hn : (transition0118Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0119Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799]
private def transition0119Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition0119Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0119Input0) = fromList transition0119Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0119 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0015 = 1 • support0037 := by
  have hs : support0015 = fromList transition0119Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0119Chunk0]
  have hn : (transition0119Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition0120Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799]
private def transition0120Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition0120Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0120Input0) = fromList transition0120Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0120 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0015 = 1 • support0036 := by
  have hs : support0015 = fromList transition0120Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0120Chunk0]
  have hn : (transition0120Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0121Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0121Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 128, 129, 136, 137, 148, 149, 156, 157, 2, 3, 10, 11, 22, 23, 30, 31, 130, 131, 138, 139, 150, 151, 158, 159]
private theorem transition0121Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0121Input0) = fromList transition0121Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0121 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0036 = 1 • support0073 := by
  have hs : support0036 = fromList transition0121Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0121Chunk0]
  have hn : (transition0121Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition0122Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0122Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 20, 21, 598, 599, 28, 29, 606, 607, 128, 129, 706, 707, 136, 137, 714, 715, 148, 149, 726, 727, 156, 157, 734, 735, 576, 577, 2, 3, 584, 585, 10, 11, 596, 597, 22, 23, 604, 605, 30, 31, 704, 705, 130, 131, 712, 713, 138, 139, 724, 725, 150, 151, 732, 733, 158, 159]
private theorem transition0122Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0122Input0) = fromList transition0122Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0122 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0036 = 1 • support0591 := by
  have hs : support0036 = fromList transition0122Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0122Chunk0]
  have hn : (transition0122Raw0 : Multiset ℕ) = 1 • (supportNumbers0591 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0591] using hm

private def transition0123Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799]
private def transition0123Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition0123Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0123Input0) = fromList transition0123Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0123 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0015 = 1 • support0593 := by
  have hs : support0015 = fromList transition0123Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0123Chunk0]
  have hn : (transition0123Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition0124Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0124Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition0124Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0124Input0) = fromList transition0124Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0124Input1 : List ℕ := [544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703, 800, 801, 802, 803, 808, 809, 810, 811, 820, 821, 822, 823, 828, 829, 830, 831, 928, 929, 930, 931, 936, 937, 938, 939, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0124Raw1 : List ℕ := [288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition0124Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0124Input1) = fromList transition0124Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0124 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0593 = 2 • support0506 := by
  have hs : support0593 = fromList transition0124Input0 + fromList transition0124Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0124Chunk0, transition0124Chunk1]
  have hn : (transition0124Raw0 : Multiset ℕ) + (transition0124Raw1 : Multiset ℕ) = 2 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm

private def transition0125Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0125Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition0125Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0125Input0) = fromList transition0125Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0125Input1 : List ℕ := [544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703, 800, 801, 802, 803, 808, 809, 810, 811, 820, 821, 822, 823, 828, 829, 830, 831, 928, 929, 930, 931, 936, 937, 938, 939, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0125Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0125Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0125Input1) = fromList transition0125Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0125 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0593 = 2 • support0508 := by
  have hs : support0593 = fromList transition0125Input0 + fromList transition0125Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0125Chunk0, transition0125Chunk1]
  have hn : (transition0125Raw0 : Multiset ℕ) + (transition0125Raw1 : Multiset ℕ) = 2 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0126Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0126Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0126Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0126Input0) = fromList transition0126Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0126 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0126Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0126Chunk0]
  have hn : (transition0126Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0127Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0127Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0127Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0127Input0) = fromList transition0127Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0127 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0127Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0127Chunk0]
  have hn : (transition0127Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0128Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0128Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0128Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0128Input0) = fromList transition0128Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0128 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0128Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0128Chunk0]
  have hn : (transition0128Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0129Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0129Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0129Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0129Input0) = fromList transition0129Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0129 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0129Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0129Chunk0]
  have hn : (transition0129Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0130Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0130Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0130Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0130Input0) = fromList transition0130Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0130 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0130Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0130Chunk0]
  have hn : (transition0130Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0131Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0131Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519]
private theorem transition0131Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0131Input0) = fromList transition0131Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0131 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0016 = 1 • support0595 := by
  have hs : support0016 = fromList transition0131Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0131Chunk0]
  have hn : (transition0131Raw0 : Multiset ℕ) = 1 • (supportNumbers0595 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0595] using hm

private def transition0132Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition0132Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0132Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0132Input0) = fromList transition0132Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0132 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0017 = 1 • support0038 := by
  have hs : support0017 = fromList transition0132Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0132Chunk0]
  have hn : (transition0132Raw0 : Multiset ℕ) = 1 • (supportNumbers0038 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0038] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
