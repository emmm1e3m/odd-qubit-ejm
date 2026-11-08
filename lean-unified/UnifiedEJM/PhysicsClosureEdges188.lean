import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3169Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
private def transition3169Raw0 : List ℕ := [0, 1, 2, 3, 532, 533, 534, 535, 8, 9, 10, 11, 540, 541, 542, 543]
private theorem transition3169Chunk0 : nextSupport ⟨false, bits4 4⟩ ⟨true, bits4 1⟩ (fromList transition3169Input0) = fromList transition3169Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3169 : nextSupport ⟨false, bits4 4⟩ ⟨true, bits4 1⟩ support1776 = 1 • support0372 := by
  have hs : support1776 = fromList transition3169Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3169Chunk0]
  have hn : (transition3169Raw0 : Multiset ℕ) = 1 • (supportNumbers0372 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0372] using hm

private def transition3170Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition3170Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition3170Chunk0 : nextSupport ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ (fromList transition3170Input0) = fromList transition3170Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3170 : nextSupport ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ support0372 = 1 • support0002 := by
  have hs : support0372 = fromList transition3170Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3170Chunk0]
  have hn : (transition3170Raw0 : Multiset ℕ) = 1 • (supportNumbers0002 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0002] using hm

private def transition3171Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition3171Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition3171Chunk0 : nextSupport ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ (fromList transition3171Input0) = fromList transition3171Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3171 : nextSupport ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ support0372 = 1 • support0003 := by
  have hs : support0372 = fromList transition3171Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3171Chunk0]
  have hn : (transition3171Raw0 : Multiset ℕ) = 1 • (supportNumbers0003 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0003] using hm

private def transition3172Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition3172Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private theorem transition3172Chunk0 : nextSupport ⟨true, bits4 4⟩ ⟨false, bits4 1⟩ (fromList transition3172Input0) = fromList transition3172Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3172 : nextSupport ⟨true, bits4 4⟩ ⟨false, bits4 1⟩ support1777 = 1 • support1778 := by
  have hs : support1777 = fromList transition3172Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3172Chunk0]
  have hn : (transition3172Raw0 : Multiset ℕ) = 1 • (supportNumbers1778 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1778] using hm

private def transition3173Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition3173Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private theorem transition3173Chunk0 : nextSupport ⟨false, bits4 1⟩ ⟨false, bits4 8⟩ (fromList transition3173Input0) = fromList transition3173Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3173 : nextSupport ⟨false, bits4 1⟩ ⟨false, bits4 8⟩ support1778 = 1 • support0004 := by
  have hs : support1778 = fromList transition3173Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3173Chunk0]
  have hn : (transition3173Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition3174Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition3174Raw0 : List ℕ := [0, 641, 2, 643, 4, 645, 6, 647, 8, 649, 10, 651, 12, 653, 14, 655, 704, 65, 706, 67, 708, 69, 710, 71, 712, 73, 714, 75, 716, 77, 718, 79]
private theorem transition3174Chunk0 : nextSupport ⟨false, bits4 1⟩ ⟨true, bits4 8⟩ (fromList transition3174Input0) = fromList transition3174Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3174 : nextSupport ⟨false, bits4 1⟩ ⟨true, bits4 8⟩ support1778 = 1 • support0005 := by
  have hs : support1778 = fromList transition3174Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3174Chunk0]
  have hn : (transition3174Raw0 : Multiset ℕ) = 1 • (supportNumbers0005 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0005] using hm

private def transition3175Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591]
private def transition3175Raw0 : List ℕ := [0, 528, 1, 529, 2, 530, 3, 531, 4, 532, 5, 533, 6, 534, 7, 535, 8, 536, 9, 537, 10, 538, 11, 539, 12, 540, 13, 541, 14, 542, 15, 543, 320, 848, 321, 849, 322, 850, 323, 851, 324, 852, 325, 853, 326, 854, 327, 855, 328, 856, 329, 857, 330, 858, 331, 859, 332, 860, 333, 861, 334, 862, 335, 863]
private theorem transition3175Chunk0 : nextSupport ⟨true, bits4 4⟩ ⟨true, bits4 1⟩ (fromList transition3175Input0) = fromList transition3175Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3175 : nextSupport ⟨true, bits4 4⟩ ⟨true, bits4 1⟩ support1777 = 1 • support1779 := by
  have hs : support1777 = fromList transition3175Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3175Chunk0]
  have hn : (transition3175Raw0 : Multiset ℕ) = 1 • (supportNumbers1779 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1779] using hm

private def transition3176Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition3176Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition3176Chunk0 : nextSupport ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ (fromList transition3176Input0) = fromList transition3176Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3176 : nextSupport ⟨true, bits4 1⟩ ⟨false, bits4 8⟩ support1779 = 1 • support0006 := by
  have hs : support1779 = fromList transition3176Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3176Chunk0]
  have hn : (transition3176Raw0 : Multiset ℕ) = 1 • (supportNumbers0006 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0006] using hm

private def transition3177Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition3177Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 272, 912, 273, 913, 274, 914, 275, 915, 276, 916, 277, 917, 278, 918, 279, 919, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 336, 976, 337, 977, 338, 978, 339, 979, 340, 980, 341, 981, 342, 982, 343, 983, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991]
private theorem transition3177Chunk0 : nextSupport ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ (fromList transition3177Input0) = fromList transition3177Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3177 : nextSupport ⟨true, bits4 1⟩ ⟨true, bits4 8⟩ support1779 = 1 • support0007 := by
  have hs : support1779 = fromList transition3177Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3177Chunk0]
  have hn : (transition3177Raw0 : Multiset ℕ) = 1 • (supportNumbers0007 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0007] using hm

private def finish0000Input0 : List ℕ := [0]
private def finish0000Raw0 : List ℕ := [0]
private theorem finish0000Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0000Input0) = fromList finish0000Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0000 : finishSupport ⟨false, bits4 4⟩ support0478 = 1 • support0478 := by
  have hs : support0478 = fromList finish0000Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0000Chunk0]
  have hn : (finish0000Raw0 : Multiset ℕ) = 1 • (supportNumbers0478 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0478] using hm

private def finish0001Input0 : List ℕ := [0, 578]
private def finish0001Raw0 : List ℕ := [0, 66]
private theorem finish0001Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0001Input0) = fromList finish0001Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0001 : finishSupport ⟨true, bits4 4⟩ support0479 = 1 • support0480 := by
  have hs : support0479 = fromList finish0001Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0001Chunk0]
  have hn : (finish0001Raw0 : Multiset ℕ) = 1 • (supportNumbers0480 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0480] using hm

private def finish0002Input0 : List ℕ := [0, 2, 296, 298]
private def finish0002Raw0 : List ℕ := [0, 2]
private theorem finish0002Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0002Input0) = fromList finish0002Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0002 : finishSupport ⟨false, bits4 4⟩ support0482 = 1 • support0008 := by
  have hs : support0482 = fromList finish0002Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0002Chunk0]
  have hn : (finish0002Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def finish0003Input0 : List ℕ := [0, 2, 296, 298, 576, 578, 872, 874]
private def finish0003Raw0 : List ℕ := [0, 2, 40, 42, 64, 66, 104, 106]
private theorem finish0003Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0003Input0) = fromList finish0003Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0003 : finishSupport ⟨true, bits4 4⟩ support0483 = 1 • support0484 := by
  have hs : support0483 = fromList finish0003Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0003Chunk0]
  have hn : (finish0003Raw0 : Multiset ℕ) = 1 • (supportNumbers0484 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0484] using hm

private def finish0004Input0 : List ℕ := [0, 8, 131, 139]
private def finish0004Raw0 : List ℕ := [0, 8, 131, 139]
private theorem finish0004Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0004Input0) = fromList finish0004Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0004 : finishSupport ⟨false, bits4 4⟩ support0485 = 1 • support0485 := by
  have hs : support0485 = fromList finish0004Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0004Chunk0]
  have hn : (finish0004Raw0 : Multiset ℕ) = 1 • (supportNumbers0485 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0485] using hm

private def finish0005Input0 : List ℕ := [0, 8, 131, 139, 578, 586, 705, 713]
private def finish0005Raw0 : List ℕ := [0, 8, 131, 139, 66, 74, 193, 201]
private theorem finish0005Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0005Input0) = fromList finish0005Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0005 : finishSupport ⟨true, bits4 4⟩ support0486 = 1 • support0487 := by
  have hs : support0486 = fromList finish0005Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0005Chunk0]
  have hn : (finish0005Raw0 : Multiset ℕ) = 1 • (supportNumbers0487 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0487] using hm

private def finish0006Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 288, 290, 296, 298, 417, 419, 425, 427]
private def finish0006Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem finish0006Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0006Input0) = fromList finish0006Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0006 : finishSupport ⟨false, bits4 4⟩ support0489 = 1 • support0268 := by
  have hs : support0489 = fromList finish0006Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0006Chunk0]
  have hn : (finish0006Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def finish0007Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 288, 290, 296, 298, 417, 419, 425, 427, 576, 578, 584, 586, 705, 707, 713, 715, 864, 866, 872, 874, 993, 995, 1001, 1003]
private def finish0007Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 32, 34, 40, 42, 161, 163, 169, 171, 64, 66, 72, 74, 193, 195, 201, 203, 96, 98, 104, 106, 225, 227, 233, 235]
private theorem finish0007Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0007Input0) = fromList finish0007Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0007 : finishSupport ⟨true, bits4 4⟩ support0490 = 1 • support0491 := by
  have hs : support0490 = fromList finish0007Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0007Chunk0]
  have hn : (finish0007Raw0 : Multiset ℕ) = 1 • (supportNumbers0491 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0491] using hm

private def finish0008Input0 : List ℕ := [0, 1, 28, 29]
private def finish0008Raw0 : List ℕ := [0, 1]
private theorem finish0008Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0008Input0) = fromList finish0008Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0008 : finishSupport ⟨false, bits4 4⟩ support0492 = 1 • support0493 := by
  have hs : support0492 = fromList finish0008Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0008Chunk0]
  have hn : (finish0008Raw0 : Multiset ℕ) = 1 • (supportNumbers0493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0493] using hm

private def finish0009Input0 : List ℕ := [0, 1, 28, 29, 578, 579, 606, 607]
private def finish0009Raw0 : List ℕ := [0, 1, 28, 29, 66, 67, 94, 95]
private theorem finish0009Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0009Input0) = fromList finish0009Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0009 : finishSupport ⟨true, bits4 4⟩ support0494 = 1 • support0495 := by
  have hs : support0494 = fromList finish0009Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0009Chunk0]
  have hn : (finish0009Raw0 : Multiset ℕ) = 1 • (supportNumbers0495 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0495] using hm

private def finish0010Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 296, 297, 298, 299, 308, 309, 310, 311]
private def finish0010Raw0 : List ℕ := [0, 1, 2, 3, 52, 53, 54, 55]
private theorem finish0010Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0010Input0) = fromList finish0010Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0010 : finishSupport ⟨false, bits4 4⟩ support0497 = 1 • support0498 := by
  have hs : support0497 = fromList finish0010Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0010Chunk0]
  have hn : (finish0010Raw0 : Multiset ℕ) = 1 • (supportNumbers0498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0498] using hm

private def finish0011Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 296, 297, 298, 299, 308, 309, 310, 311, 576, 577, 578, 579, 604, 605, 606, 607, 872, 873, 874, 875, 884, 885, 886, 887]
private def finish0011Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 40, 41, 42, 43, 52, 53, 54, 55, 64, 65, 66, 67, 92, 93, 94, 95, 104, 105, 106, 107, 116, 117, 118, 119]
private theorem finish0011Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0011Input0) = fromList finish0011Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0011 : finishSupport ⟨true, bits4 4⟩ support0499 = 1 • support0500 := by
  have hs : support0499 = fromList finish0011Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0011Chunk0]
  have hn : (finish0011Raw0 : Multiset ℕ) = 1 • (supportNumbers0500 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0500] using hm

private def finish0012Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 130, 131, 138, 139, 150, 151, 158, 159]
private def finish0012Raw0 : List ℕ := [0, 1, 8, 9, 130, 131, 138, 139]
private theorem finish0012Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0012Input0) = fromList finish0012Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0012 : finishSupport ⟨false, bits4 4⟩ support0501 = 1 • support0502 := by
  have hs : support0501 = fromList finish0012Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0012Chunk0]
  have hn : (finish0012Raw0 : Multiset ℕ) = 1 • (supportNumbers0502 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0502] using hm

private def finish0013Input0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 130, 131, 138, 139, 150, 151, 158, 159, 578, 579, 586, 587, 598, 599, 606, 607, 704, 705, 712, 713, 724, 725, 732, 733]
private def finish0013Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 130, 131, 138, 139, 150, 151, 158, 159, 66, 67, 74, 75, 86, 87, 94, 95, 192, 193, 200, 201, 212, 213, 220, 221]
private theorem finish0013Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0013Input0) = fromList finish0013Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0013 : finishSupport ⟨true, bits4 4⟩ support0503 = 1 • support0504 := by
  have hs : support0503 = fromList finish0013Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0013Chunk0]
  have hn : (finish0013Raw0 : Multiset ℕ) = 1 • (supportNumbers0504 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0504] using hm

private def finish0014Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private def finish0014Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 52, 53, 54, 55, 60, 61, 62, 63, 180, 181, 182, 183, 188, 189, 190, 191]
private theorem finish0014Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0014Input0) = fromList finish0014Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0014 : finishSupport ⟨false, bits4 4⟩ support0506 = 1 • support0507 := by
  have hs : support0506 = fromList finish0014Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0014Chunk0]
  have hn : (finish0014Raw0 : Multiset ℕ) = 1 • (supportNumbers0507 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0507] using hm

private def finish0015Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private def finish0015Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 32, 33, 34, 35, 40, 41, 42, 43, 52, 53, 54, 55, 60, 61, 62, 63, 160, 161, 162, 163, 168, 169, 170, 171, 180, 181, 182, 183, 188, 189, 190, 191]
private theorem finish0015Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0015Input0) = fromList finish0015Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0015Input1 : List ℕ := [576, 577, 578, 579, 584, 585, 586, 587, 596, 597, 598, 599, 604, 605, 606, 607, 704, 705, 706, 707, 712, 713, 714, 715, 724, 725, 726, 727, 732, 733, 734, 735, 864, 865, 866, 867, 872, 873, 874, 875, 884, 885, 886, 887, 892, 893, 894, 895, 992, 993, 994, 995, 1000, 1001, 1002, 1003, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]
private def finish0015Raw1 : List ℕ := [64, 65, 66, 67, 72, 73, 74, 75, 84, 85, 86, 87, 92, 93, 94, 95, 192, 193, 194, 195, 200, 201, 202, 203, 212, 213, 214, 215, 220, 221, 222, 223, 96, 97, 98, 99, 104, 105, 106, 107, 116, 117, 118, 119, 124, 125, 126, 127, 224, 225, 226, 227, 232, 233, 234, 235, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0015Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0015Input1) = fromList finish0015Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0015 : finishSupport ⟨true, bits4 4⟩ support0508 = 1 • support0509 := by
  have hs : support0508 = fromList finish0015Input0 + fromList finish0015Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0015Chunk0, finish0015Chunk1]
  have hn : (finish0015Raw0 : Multiset ℕ) + (finish0015Raw1 : Multiset ℕ) = 1 • (supportNumbers0509 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0509] using hm

private def finish0016Input0 : List ℕ := [0, 4, 65, 69]
private def finish0016Raw0 : List ℕ := [0, 65]
private theorem finish0016Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0016Input0) = fromList finish0016Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0016 : finishSupport ⟨false, bits4 4⟩ support0510 = 1 • support0511 := by
  have hs : support0510 = fromList finish0016Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0016Chunk0]
  have hn : (finish0016Raw0 : Multiset ℕ) = 1 • (supportNumbers0511 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0511] using hm

private def finish0017Input0 : List ℕ := [0, 4, 65, 69, 515, 519, 578, 582]
private def finish0017Raw0 : List ℕ := [0, 4, 65, 69, 3, 7, 66, 70]
private theorem finish0017Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0017Input0) = fromList finish0017Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0017 : finishSupport ⟨true, bits4 4⟩ support0512 = 1 • support0513 := by
  have hs : support0512 = fromList finish0017Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0017Chunk0]
  have hn : (finish0017Raw0 : Multiset ℕ) = 1 • (supportNumbers0513 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0513] using hm

private def finish0018Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 296, 298, 300, 302, 361, 363, 365, 367]
private def finish0018Raw0 : List ℕ := [0, 2, 65, 67, 44, 46, 109, 111]
private theorem finish0018Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0018Input0) = fromList finish0018Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0018 : finishSupport ⟨false, bits4 4⟩ support0515 = 1 • support0516 := by
  have hs : support0515 = fromList finish0018Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0018Chunk0]
  have hn : (finish0018Raw0 : Multiset ℕ) = 1 • (supportNumbers0516 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0516] using hm

private def finish0019Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 296, 298, 300, 302, 361, 363, 365, 367, 513, 515, 517, 519, 576, 578, 580, 582, 809, 811, 813, 815, 872, 874, 876, 878]
private def finish0019Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 40, 42, 44, 46, 105, 107, 109, 111, 1, 3, 5, 7, 64, 66, 68, 70, 41, 43, 45, 47, 104, 106, 108, 110]
private theorem finish0019Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0019Input0) = fromList finish0019Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0019 : finishSupport ⟨true, bits4 4⟩ support0517 = 1 • support0518 := by
  have hs : support0517 = fromList finish0019Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0019Chunk0]
  have hn : (finish0019Raw0 : Multiset ℕ) = 1 • (supportNumbers0518 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0518] using hm

private def finish0020Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 131, 135, 139, 143, 194, 198, 202, 206]
private def finish0020Raw0 : List ℕ := [0, 8, 65, 73, 131, 139, 194, 202]
private theorem finish0020Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0020Input0) = fromList finish0020Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0020 : finishSupport ⟨false, bits4 4⟩ support0519 = 1 • support0520 := by
  have hs : support0519 = fromList finish0020Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0020Chunk0]
  have hn : (finish0020Raw0 : Multiset ℕ) = 1 • (supportNumbers0520 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0520] using hm

private def finish0021Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 131, 135, 139, 143, 194, 198, 202, 206, 515, 519, 523, 527, 578, 582, 586, 590, 640, 644, 648, 652, 705, 709, 713, 717]
private def finish0021Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 131, 135, 139, 143, 194, 198, 202, 206, 3, 7, 11, 15, 66, 70, 74, 78, 128, 132, 136, 140, 193, 197, 201, 205]
private theorem finish0021Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0021Input0) = fromList finish0021Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0021 : finishSupport ⟨true, bits4 4⟩ support0521 = 1 • support0522 := by
  have hs : support0521 = fromList finish0021Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0021Chunk0]
  have hn : (finish0021Raw0 : Multiset ℕ) = 1 • (supportNumbers0522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0522] using hm

private def finish0022Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494]
private def finish0022Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 129, 131, 137, 139, 192, 194, 200, 202, 36, 38, 44, 46, 101, 103, 109, 111, 165, 167, 173, 175, 228, 230, 236, 238]
private theorem finish0022Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0022Input0) = fromList finish0022Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0022 : finishSupport ⟨false, bits4 4⟩ support0524 = 1 • support0525 := by
  have hs : support0524 = fromList finish0022Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0022Chunk0]
  have hn : (finish0022Raw0 : Multiset ℕ) = 1 • (supportNumbers0525 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0525] using hm

private def finish0023Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494]
private def finish0023Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 32, 34, 36, 38, 40, 42, 44, 46, 97, 99, 101, 103, 105, 107, 109, 111, 161, 163, 165, 167, 169, 171, 173, 175, 224, 226, 228, 230, 232, 234, 236, 238]
private theorem finish0023Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0023Input0) = fromList finish0023Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0023Input1 : List ℕ := [513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 640, 642, 644, 646, 648, 650, 652, 654, 705, 707, 709, 711, 713, 715, 717, 719, 801, 803, 805, 807, 809, 811, 813, 815, 864, 866, 868, 870, 872, 874, 876, 878, 928, 930, 932, 934, 936, 938, 940, 942, 993, 995, 997, 999, 1001, 1003, 1005, 1007]
private def finish0023Raw1 : List ℕ := [1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 33, 35, 37, 39, 41, 43, 45, 47, 96, 98, 100, 102, 104, 106, 108, 110, 160, 162, 164, 166, 168, 170, 172, 174, 225, 227, 229, 231, 233, 235, 237, 239]
private theorem finish0023Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0023Input1) = fromList finish0023Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0023 : finishSupport ⟨true, bits4 4⟩ support0526 = 1 • support0527 := by
  have hs : support0526 = fromList finish0023Input0 + fromList finish0023Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0023Chunk0, finish0023Chunk1]
  have hn : (finish0023Raw0 : Multiset ℕ) + (finish0023Raw1 : Multiset ℕ) = 1 • (supportNumbers0527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0527] using hm

private def finish0024Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93]
private def finish0024Raw0 : List ℕ := [0, 1, 24, 25, 64, 65, 88, 89]
private theorem finish0024Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0024Input0) = fromList finish0024Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0024 : finishSupport ⟨false, bits4 4⟩ support0528 = 1 • support0529 := by
  have hs : support0528 = fromList finish0024Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0024Chunk0]
  have hn : (finish0024Raw0 : Multiset ℕ) = 1 • (supportNumbers0529 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0529] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
