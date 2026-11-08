import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0491Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition0491Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition0491Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0491Input0) = fromList transition0491Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0491 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0062 = 2 • support0062 := by
  have hs : support0062 = fromList transition0491Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0491Chunk0]
  have hn : (transition0491Raw0 : Multiset ℕ) = 2 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition0492Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition0492Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition0492Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0492Input0) = fromList transition0492Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0492 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0062 = 2 • support0061 := by
  have hs : support0062 = fromList transition0492Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0492Chunk0]
  have hn : (transition0492Raw0 : Multiset ℕ) = 2 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0493Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition0493Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition0493Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0493Input0) = fromList transition0493Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0493 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0062 = 2 • support0680 := by
  have hs : support0062 = fromList transition0493Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0493Chunk0]
  have hn : (transition0493Raw0 : Multiset ℕ) = 2 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition0494Input0 : List ℕ := [0, 1, 2, 3]
private def transition0494Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0494Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0494Input0) = fromList transition0494Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0494 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0494Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0494Chunk0]
  have hn : (transition0494Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0495Input0 : List ℕ := [0, 1, 2, 3]
private def transition0495Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643]
private theorem transition0495Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0495Input0) = fromList transition0495Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0495 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0030 = 1 • support0116 := by
  have hs : support0030 = fromList transition0495Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0495Chunk0]
  have hn : (transition0495Raw0 : Multiset ℕ) = 1 • (supportNumbers0116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0116] using hm

private def transition0496Input0 : List ℕ := [0, 1, 2, 3]
private def transition0496Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0496Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0496Input0) = fromList transition0496Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0496 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0496Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0496Chunk0]
  have hn : (transition0496Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0497Input0 : List ℕ := [0, 1, 2, 3]
private def transition0497Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547]
private theorem transition0497Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0497Input0) = fromList transition0497Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0497 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0030 = 1 • support0847 := by
  have hs : support0030 = fromList transition0497Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0497Chunk0]
  have hn : (transition0497Raw0 : Multiset ℕ) = 1 • (supportNumbers0847 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0847] using hm

private def transition0498Input0 : List ℕ := [0, 1, 2, 3, 544, 545, 546, 547]
private def transition0498Raw0 : List ℕ := [0, 1, 2, 3, 288, 289, 290, 291]
private theorem transition0498Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0498Input0) = fromList transition0498Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0498 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0847 = 1 • support0848 := by
  have hs : support0847 = fromList transition0498Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0498Chunk0]
  have hn : (transition0498Raw0 : Multiset ℕ) = 1 • (supportNumbers0848 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0848] using hm

private def transition0499Input0 : List ℕ := [0, 1, 2, 3, 544, 545, 546, 547]
private def transition0499Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 288, 864, 289, 865, 290, 866, 291, 867]
private theorem transition0499Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0499Input0) = fromList transition0499Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0499 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0847 = 1 • support0849 := by
  have hs : support0847 = fromList transition0499Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0499Chunk0]
  have hn : (transition0499Raw0 : Multiset ℕ) = 1 • (supportNumbers0849 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0849] using hm

private def transition0500Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0500Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0500Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0500Input0) = fromList transition0500Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0500 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0063 = 1 • support0117 := by
  have hs : support0063 = fromList transition0500Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0500Chunk0]
  have hn : (transition0500Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0501Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0501Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0501Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0501Input0) = fromList transition0501Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0501 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0063 = 1 • support0117 := by
  have hs : support0063 = fromList transition0501Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0501Chunk0]
  have hn : (transition0501Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0502Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0502Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0502Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0502Input0) = fromList transition0502Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0502 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0063 = 1 • support0117 := by
  have hs : support0063 = fromList transition0502Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0502Chunk0]
  have hn : (transition0502Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0503Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0503Raw0 : List ℕ := [0, 1, 156, 157]
private theorem transition0503Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0503Input0) = fromList transition0503Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0503 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0117 = 1 • support0851 := by
  have hs : support0117 = fromList transition0503Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0503Chunk0]
  have hn : (transition0503Raw0 : Multiset ℕ) = 1 • (supportNumbers0851 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0851] using hm

private def transition0504Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0504Raw0 : List ℕ := [0, 1, 578, 579, 156, 157, 734, 735]
private theorem transition0504Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0504Input0) = fromList transition0504Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0504 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0117 = 1 • support0852 := by
  have hs : support0117 = fromList transition0504Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0504Chunk0]
  have hn : (transition0504Raw0 : Multiset ℕ) = 1 • (supportNumbers0852 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0852] using hm

private def transition0505Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0505Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0505Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0505Input0) = fromList transition0505Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0505 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0063 = 1 • support0117 := by
  have hs : support0063 = fromList transition0505Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0505Chunk0]
  have hn : (transition0505Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0506Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0506Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0506Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0506Input0) = fromList transition0506Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0506 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0117 = 1 • support0117 := by
  have hs : support0117 = fromList transition0506Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0506Chunk0]
  have hn : (transition0506Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0507Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0507Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition0507Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0507Input0) = fromList transition0507Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0507 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0117 = 1 • support0854 := by
  have hs : support0117 = fromList transition0507Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0507Chunk0]
  have hn : (transition0507Raw0 : Multiset ℕ) = 1 • (supportNumbers0854 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0854] using hm

private def transition0508Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 640, 641, 642, 643, 796, 797, 798, 799]
private def transition0508Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 384, 385, 386, 387, 284, 285, 286, 287]
private theorem transition0508Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0508Input0) = fromList transition0508Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0508 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0064 = 1 • support0118 := by
  have hs : support0064 = fromList transition0508Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0508Chunk0]
  have hn : (transition0508Raw0 : Multiset ℕ) = 1 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition0509Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 640, 641, 642, 643, 796, 797, 798, 799]
private def transition0509Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 384, 768, 385, 769, 386, 770, 387, 771, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition0509Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0509Input0) = fromList transition0509Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0509 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0064 = 1 • support0119 := by
  have hs : support0064 = fromList transition0509Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0509Chunk0]
  have hn : (transition0509Raw0 : Multiset ℕ) = 1 • (supportNumbers0119 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0119] using hm

private def transition0510Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 640, 641, 642, 643, 796, 797, 798, 799]
private def transition0510Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 384, 385, 386, 387, 284, 285, 286, 287]
private theorem transition0510Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0510Input0) = fromList transition0510Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0510 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0064 = 1 • support0118 := by
  have hs : support0064 = fromList transition0510Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0510Chunk0]
  have hn : (transition0510Raw0 : Multiset ℕ) = 1 • (supportNumbers0118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0118] using hm

private def transition0511Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0511Raw0 : List ℕ := [0, 1, 156, 157, 30, 31, 130, 131]
private theorem transition0511Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0511Input0) = fromList transition0511Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0511 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0118 = 1 • support0856 := by
  have hs : support0118 = fromList transition0511Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0511Chunk0]
  have hn : (transition0511Raw0 : Multiset ℕ) = 1 • (supportNumbers0856 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0856] using hm

private def transition0512Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0512Raw0 : List ℕ := [0, 1, 578, 579, 156, 157, 734, 735, 604, 605, 30, 31, 704, 705, 130, 131]
private theorem transition0512Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0512Input0) = fromList transition0512Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0512 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0118 = 1 • support0858 := by
  have hs : support0118 = fromList transition0512Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0512Chunk0]
  have hn : (transition0512Raw0 : Multiset ℕ) = 1 • (supportNumbers0858 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0858] using hm

private def transition0513Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 640, 641, 642, 643, 796, 797, 798, 799]
private def transition0513Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 384, 928, 385, 929, 386, 930, 387, 931, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition0513Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0513Input0) = fromList transition0513Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0513 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0064 = 1 • support0860 := by
  have hs : support0064 = fromList transition0513Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0513Chunk0]
  have hn : (transition0513Raw0 : Multiset ℕ) = 1 • (supportNumbers0860 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0860] using hm

private def transition0514Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 544, 545, 546, 547, 700, 701, 702, 703, 828, 829, 830, 831, 928, 929, 930, 931]
private def transition0514Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 28, 29, 30, 31, 128, 129, 130, 131, 288, 289, 290, 291, 444, 445, 446, 447, 316, 317, 318, 319, 416, 417, 418, 419]
private theorem transition0514Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0514Input0) = fromList transition0514Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0514 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0860 = 1 • support0861 := by
  have hs : support0860 = fromList transition0514Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0514Chunk0]
  have hn : (transition0514Raw0 : Multiset ℕ) = 1 • (supportNumbers0861 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0861] using hm

private def transition0515Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 544, 545, 546, 547, 700, 701, 702, 703, 828, 829, 830, 831, 928, 929, 930, 931]
private def transition0515Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition0515Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0515Input0) = fromList transition0515Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0515 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0860 = 1 • support0863 := by
  have hs : support0860 = fromList transition0515Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0515Chunk0]
  have hn : (transition0515Raw0 : Multiset ℕ) = 1 • (supportNumbers0863 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0863] using hm

private def transition0516Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0516Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0516Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0516Input0) = fromList transition0516Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0516 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0065 = 1 • support0030 := by
  have hs : support0065 = fromList transition0516Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0516Chunk0]
  have hn : (transition0516Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0517Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0517Raw0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523]
private theorem transition0517Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0517Input0) = fromList transition0517Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0517 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0065 = 1 • support0120 := by
  have hs : support0065 = fromList transition0517Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0517Chunk0]
  have hn : (transition0517Raw0 : Multiset ℕ) = 1 • (supportNumbers0120 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0120] using hm

private def transition0518Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0518Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0518Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0518Input0) = fromList transition0518Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0518 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0065 = 1 • support0030 := by
  have hs : support0065 = fromList transition0518Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0518Chunk0]
  have hn : (transition0518Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0519Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0519Raw0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683]
private theorem transition0519Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0519Input0) = fromList transition0519Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0519 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0065 = 1 • support0865 := by
  have hs : support0065 = fromList transition0519Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0519Chunk0]
  have hn : (transition0519Raw0 : Multiset ℕ) = 1 • (supportNumbers0865 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0865] using hm

private def transition0520Input0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683]
private def transition0520Raw0 : List ℕ := [0, 1, 2, 3, 424, 425, 426, 427]
private theorem transition0520Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0520Input0) = fromList transition0520Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0520 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0865 = 1 • support0866 := by
  have hs : support0865 = fromList transition0520Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0520Chunk0]
  have hn : (transition0520Raw0 : Multiset ℕ) = 1 • (supportNumbers0866 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0866] using hm

private def transition0521Input0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683]
private def transition0521Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0521Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0521Input0) = fromList transition0521Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0521 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0865 = 1 • support0867 := by
  have hs : support0865 = fromList transition0521Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0521Chunk0]
  have hn : (transition0521Raw0 : Multiset ℕ) = 1 • (supportNumbers0867 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0867] using hm

private def transition0522Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 532, 533, 534, 535, 668, 669, 670, 671]
private def transition0522Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private theorem transition0522Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0522Input0) = fromList transition0522Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0522 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0066 = 1 • support0121 := by
  have hs : support0066 = fromList transition0522Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0522Chunk0]
  have hn : (transition0522Raw0 : Multiset ℕ) = 1 • (supportNumbers0121 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0121] using hm

private def transition0523Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 532, 533, 534, 535, 668, 669, 670, 671]
private def transition0523Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 276, 916, 277, 917, 278, 918, 279, 919, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0523Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0523Input0) = fromList transition0523Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0523 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0066 = 1 • support0122 := by
  have hs : support0066 = fromList transition0523Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0523Chunk0]
  have hn : (transition0523Raw0 : Multiset ℕ) = 1 • (supportNumbers0122 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0122] using hm

private def transition0524Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 532, 533, 534, 535, 668, 669, 670, 671]
private def transition0524Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private theorem transition0524Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0524Input0) = fromList transition0524Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0524 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0066 = 1 • support0121 := by
  have hs : support0066 = fromList transition0524Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0524Chunk0]
  have hn : (transition0524Raw0 : Multiset ℕ) = 1 • (supportNumbers0121 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0121] using hm

private def transition0525Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0525Raw0 : List ℕ := [0, 1, 136, 137, 22, 23, 158, 159]
private theorem transition0525Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0525Input0) = fromList transition0525Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0525 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0121 = 1 • support0869 := by
  have hs : support0121 = fromList transition0525Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0525Chunk0]
  have hn : (transition0525Raw0 : Multiset ℕ) = 1 • (supportNumbers0869 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0869] using hm

private def transition0526Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0526Raw0 : List ℕ := [0, 1, 578, 579, 136, 137, 714, 715, 596, 597, 22, 23, 732, 733, 158, 159]
private theorem transition0526Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0526Input0) = fromList transition0526Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0526 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0121 = 1 • support0870 := by
  have hs : support0121 = fromList transition0526Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0526Chunk0]
  have hn : (transition0526Raw0 : Multiset ℕ) = 1 • (supportNumbers0870 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0870] using hm

private def transition0527Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 532, 533, 534, 535, 668, 669, 670, 671]
private def transition0527Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 276, 820, 277, 821, 278, 822, 279, 823, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0527Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0527Input0) = fromList transition0527Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0527 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0066 = 1 • support0872 := by
  have hs : support0066 = fromList transition0527Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0527Chunk0]
  have hn : (transition0527Raw0 : Multiset ℕ) = 1 • (supportNumbers0872 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0872] using hm

private def transition0528Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 544, 545, 546, 547, 680, 681, 682, 683, 820, 821, 822, 823, 956, 957, 958, 959]
private def transition0528Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 20, 21, 22, 23, 156, 157, 158, 159, 288, 289, 290, 291, 424, 425, 426, 427, 308, 309, 310, 311, 444, 445, 446, 447]
private theorem transition0528Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0528Input0) = fromList transition0528Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0528 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0872 = 1 • support0712 := by
  have hs : support0872 = fromList transition0528Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0528Chunk0]
  have hn : (transition0528Raw0 : Multiset ℕ) = 1 • (supportNumbers0712 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0712] using hm

private def transition0529Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 544, 545, 546, 547, 680, 681, 682, 683, 820, 821, 822, 823, 956, 957, 958, 959]
private def transition0529Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 20, 596, 21, 597, 22, 598, 23, 599, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 308, 884, 309, 885, 310, 886, 311, 887, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0529Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0529Input0) = fromList transition0529Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0529 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0872 = 1 • support0714 := by
  have hs : support0872 = fromList transition0529Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0529Chunk0]
  have hn : (transition0529Raw0 : Multiset ℕ) = 1 • (supportNumbers0714 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0714] using hm

private def transition0530Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0530Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition0530Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0530Input0) = fromList transition0530Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0530 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0067 = 1 • support0123 := by
  have hs : support0067 = fromList transition0530Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0530Chunk0]
  have hn : (transition0530Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition0531Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0531Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 520, 521, 522, 523, 148, 149, 150, 151, 8, 9, 10, 11, 660, 661, 662, 663, 512, 513, 514, 515, 156, 157, 158, 159]
private theorem transition0531Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0531Input0) = fromList transition0531Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0531 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0067 = 1 • support0124 := by
  have hs : support0067 = fromList transition0531Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0531Chunk0]
  have hn : (transition0531Raw0 : Multiset ℕ) = 1 • (supportNumbers0124 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0124] using hm

private def transition0532Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0532Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition0532Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0532Input0) = fromList transition0532Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0532 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0067 = 1 • support0123 := by
  have hs : support0067 = fromList transition0532Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0532Chunk0]
  have hn : (transition0532Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition0533Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0533Raw0 : List ℕ := [0, 1, 8, 9, 148, 149, 156, 157]
private theorem transition0533Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0533Input0) = fromList transition0533Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0533 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0123 = 1 • support0873 := by
  have hs : support0123 = fromList transition0533Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0533Chunk0]
  have hn : (transition0533Raw0 : Multiset ℕ) = 1 • (supportNumbers0873 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0873] using hm

private def transition0534Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0534Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 148, 149, 726, 727, 156, 157, 734, 735]
private theorem transition0534Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0534Input0) = fromList transition0534Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0534 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0123 = 1 • support0875 := by
  have hs : support0123 = fromList transition0534Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0534Chunk0]
  have hn : (transition0534Raw0 : Multiset ℕ) = 1 • (supportNumbers0875 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0875] using hm

private def transition0535Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0535Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 680, 681, 682, 683, 148, 149, 150, 151, 8, 9, 10, 11, 564, 565, 566, 567, 672, 673, 674, 675, 156, 157, 158, 159]
private theorem transition0535Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0535Input0) = fromList transition0535Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0535 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0067 = 1 • support0877 := by
  have hs : support0067 = fromList transition0535Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0535Chunk0]
  have hn : (transition0535Raw0 : Multiset ℕ) = 1 • (supportNumbers0877 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0877] using hm

private def transition0536Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0536Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition0536Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0536Input0) = fromList transition0536Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0536 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0877 = 1 • support0878 := by
  have hs : support0877 = fromList transition0536Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0536Chunk0]
  have hn : (transition0536Raw0 : Multiset ℕ) = 1 • (supportNumbers0878 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0878] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
