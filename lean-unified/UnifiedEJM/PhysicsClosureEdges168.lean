import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2909Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 544, 545, 546, 547, 692, 693, 694, 695, 808, 809, 810, 811, 956, 957, 958, 959]
private def transition2909Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 8, 584, 9, 585, 10, 586, 11, 587, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 296, 872, 297, 873, 298, 874, 299, 875, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2909Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2909Input0) = fromList transition2909Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2909 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1753 = 1 • support1118 := by
  have hs : support1753 = fromList transition2909Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2909Chunk0]
  have hn : (transition2909Raw0 : Multiset ℕ) = 1 • (supportNumbers1118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1118] using hm

private def transition2910Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2910Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2910Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2910Input0) = fromList transition2910Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2910 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0432 = 1 • support0067 := by
  have hs : support0432 = fromList transition2910Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2910Chunk0]
  have hn : (transition2910Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2911Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2911Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2911Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2911Input0) = fromList transition2911Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2911 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0432 = 1 • support0068 := by
  have hs : support0432 = fromList transition2911Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2911Chunk0]
  have hn : (transition2911Raw0 : Multiset ℕ) = 1 • (supportNumbers0068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0068] using hm

private def transition2912Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2912Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2912Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2912Input0) = fromList transition2912Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2912 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0432 = 1 • support0067 := by
  have hs : support0432 = fromList transition2912Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2912Chunk0]
  have hn : (transition2912Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2913Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2913Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2913Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2913Input0) = fromList transition2913Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2913 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0432 = 1 • support0701 := by
  have hs : support0432 = fromList transition2913Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2913Chunk0]
  have hn : (transition2913Raw0 : Multiset ℕ) = 1 • (supportNumbers0701 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0701] using hm

private def transition2914Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2914Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2914Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2914Input0) = fromList transition2914Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2914 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0433 = 1 • support0374 := by
  have hs : support0433 = fromList transition2914Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2914Chunk0]
  have hn : (transition2914Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2915Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2915Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 520, 521, 522, 523, 148, 149, 150, 151, 640, 641, 642, 643, 28, 29, 30, 31, 136, 137, 138, 139, 532, 533, 534, 535]
private theorem transition2915Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2915Input0) = fromList transition2915Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2915 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0433 = 1 • support0432 := by
  have hs : support0433 = fromList transition2915Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2915Chunk0]
  have hn : (transition2915Raw0 : Multiset ℕ) = 1 • (supportNumbers0432 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0432] using hm

private def transition2916Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2916Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2916Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2916Input0) = fromList transition2916Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2916 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0433 = 1 • support0374 := by
  have hs : support0433 = fromList transition2916Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2916Chunk0]
  have hn : (transition2916Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2917Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2917Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 680, 681, 682, 683, 148, 149, 150, 151, 544, 545, 546, 547, 28, 29, 30, 31, 136, 137, 138, 139, 692, 693, 694, 695]
private theorem transition2917Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2917Input0) = fromList transition2917Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2917 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0433 = 1 • support1686 := by
  have hs : support0433 = fromList transition2917Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2917Chunk0]
  have hn : (transition2917Raw0 : Multiset ℕ) = 1 • (supportNumbers1686 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1686] using hm

private def transition2918Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition2918Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2918Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2918Input0) = fromList transition2918Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2918 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0434 = 2 • support0067 := by
  have hs : support0434 = fromList transition2918Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2918Chunk0]
  have hn : (transition2918Raw0 : Multiset ℕ) = 2 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2919Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition2919Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2919Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2919Input0) = fromList transition2919Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2919 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0434 = 2 • support0068 := by
  have hs : support0434 = fromList transition2919Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2919Chunk0]
  have hn : (transition2919Raw0 : Multiset ℕ) = 2 • (supportNumbers0068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0068] using hm

private def transition2920Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition2920Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2920Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2920Input0) = fromList transition2920Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2920 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0434 = 2 • support0067 := by
  have hs : support0434 = fromList transition2920Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2920Chunk0]
  have hn : (transition2920Raw0 : Multiset ℕ) = 2 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2921Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition2921Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2921Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2921Input0) = fromList transition2921Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2921 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0434 = 2 • support0701 := by
  have hs : support0434 = fromList transition2921Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2921Chunk0]
  have hn : (transition2921Raw0 : Multiset ℕ) = 2 • (supportNumbers0701 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0701] using hm

private def transition2922Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2922Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition2922Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2922Input0) = fromList transition2922Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2922 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0435 = 1 • support0069 := by
  have hs : support0435 = fromList transition2922Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2922Chunk0]
  have hn : (transition2922Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition2923Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2923Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 640, 641, 642, 643, 660, 661, 662, 663]
private theorem transition2923Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2923Input0) = fromList transition2923Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2923 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0435 = 1 • support0203 := by
  have hs : support0435 = fromList transition2923Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2923Chunk0]
  have hn : (transition2923Raw0 : Multiset ℕ) = 1 • (supportNumbers0203 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0203] using hm

private def transition2924Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2924Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition2924Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2924Input0) = fromList transition2924Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2924 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0435 = 1 • support0069 := by
  have hs : support0435 = fromList transition2924Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2924Chunk0]
  have hn : (transition2924Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition2925Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2925Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 544, 545, 546, 547, 564, 565, 566, 567]
private theorem transition2925Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2925Input0) = fromList transition2925Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2925 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0435 = 1 • support1120 := by
  have hs : support0435 = fromList transition2925Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2925Chunk0]
  have hn : (transition2925Raw0 : Multiset ℕ) = 1 • (supportNumbers1120 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1120] using hm

private def transition2926Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 640, 641, 642, 643, 660, 661, 662, 663, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2926Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2926Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2926Input0) = fromList transition2926Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2926 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0436 = 2 • support0290 := by
  have hs : support0436 = fromList transition2926Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2926Chunk0]
  have hn : (transition2926Raw0 : Multiset ℕ) = 2 • (supportNumbers0290 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0290] using hm

private def transition2927Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 640, 641, 642, 643, 660, 661, 662, 663, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2927Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition2927Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2927Input0) = fromList transition2927Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2927 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0436 = 2 • support0291 := by
  have hs : support0436 = fromList transition2927Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2927Chunk0]
  have hn : (transition2927Raw0 : Multiset ℕ) = 2 • (supportNumbers0291 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0291] using hm

private def transition2928Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 640, 641, 642, 643, 660, 661, 662, 663, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2928Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2928Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2928Input0) = fromList transition2928Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2928 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0436 = 2 • support0290 := by
  have hs : support0436 = fromList transition2928Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2928Chunk0]
  have hn : (transition2928Raw0 : Multiset ℕ) = 2 • (supportNumbers0290 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0290] using hm

private def transition2929Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 640, 641, 642, 643, 660, 661, 662, 663, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2929Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition2929Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2929Input0) = fromList transition2929Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2929 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0436 = 2 • support1359 := by
  have hs : support0436 = fromList transition2929Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2929Chunk0]
  have hn : (transition2929Raw0 : Multiset ℕ) = 2 • (supportNumbers1359 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1359] using hm

private def transition2930Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2930Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2930Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2930Input0) = fromList transition2930Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2930 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0034 = 1 • support0034 := by
  have hs : support0034 = fromList transition2930Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2930Chunk0]
  have hn : (transition2930Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2931Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2931Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543]
private theorem transition2931Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2931Input0) = fromList transition2931Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2931 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0034 = 1 • support0127 := by
  have hs : support0034 = fromList transition2931Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2931Chunk0]
  have hn : (transition2931Raw0 : Multiset ℕ) = 1 • (supportNumbers0127 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0127] using hm

private def transition2932Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2932Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2932Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2932Input0) = fromList transition2932Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2932 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0034 = 1 • support0034 := by
  have hs : support0034 = fromList transition2932Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2932Chunk0]
  have hn : (transition2932Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2933Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2933Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703]
private theorem transition2933Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2933Input0) = fromList transition2933Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2933 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0034 = 1 • support0892 := by
  have hs : support0034 = fromList transition2933Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2933Chunk0]
  have hn : (transition2933Raw0 : Multiset ℕ) = 1 • (supportNumbers0892 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0892] using hm

private def transition2934Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2934Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2934Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2934Input0) = fromList transition2934Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2934 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0437 = 1 • support0076 := by
  have hs : support0437 = fromList transition2934Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2934Chunk0]
  have hn : (transition2934Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition2935Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2935Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition2935Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2935Input0) = fromList transition2935Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2935 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0437 = 1 • support0135 := by
  have hs : support0437 = fromList transition2935Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2935Chunk0]
  have hn : (transition2935Raw0 : Multiset ℕ) = 1 • (supportNumbers0135 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0135] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
