import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0000Input0 : List ℕ := [0, 2, 8, 10]
private def transition0000Raw0 : List ℕ := [0, 2]
private theorem transition0000Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0000Input0) = fromList transition0000Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0000 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0000 = 1 • support0008 := by
  have hs : support0000 = fromList transition0000Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0000Chunk0]
  have hn : (transition0000Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0001Input0 : List ℕ := [0, 2, 8, 10]
private def transition0001Raw0 : List ℕ := [0, 2, 648, 650]
private theorem transition0001Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0001Input0) = fromList transition0001Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0001 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0000 = 1 • support0009 := by
  have hs : support0000 = fromList transition0001Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0001Chunk0]
  have hn : (transition0001Raw0 : Multiset ℕ) = 1 • (supportNumbers0009 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0009] using hm

private def transition0002Input0 : List ℕ := [0, 2, 8, 10]
private def transition0002Raw0 : List ℕ := [0, 2]
private theorem transition0002Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0002Input0) = fromList transition0002Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0002 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0000 = 1 • support0008 := by
  have hs : support0000 = fromList transition0002Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0002Chunk0]
  have hn : (transition0002Raw0 : Multiset ℕ) = 1 • (supportNumbers0008 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0008] using hm

private def transition0003Input0 : List ℕ := [0, 2]
private def transition0003Raw0 : List ℕ := [0]
private theorem transition0003Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0003Input0) = fromList transition0003Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0003 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0008 = 1 • support0478 := by
  have hs : support0008 = fromList transition0003Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0003Chunk0]
  have hn : (transition0003Raw0 : Multiset ℕ) = 1 • (supportNumbers0478 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0478] using hm

private def transition0004Input0 : List ℕ := [0, 2]
private def transition0004Raw0 : List ℕ := [0, 578]
private theorem transition0004Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0004Input0) = fromList transition0004Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0004 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0008 = 1 • support0479 := by
  have hs : support0008 = fromList transition0004Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0004Chunk0]
  have hn : (transition0004Raw0 : Multiset ℕ) = 1 • (supportNumbers0479 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0479] using hm

private def transition0005Input0 : List ℕ := [0, 2, 8, 10]
private def transition0005Raw0 : List ℕ := [0, 2, 552, 554]
private theorem transition0005Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0005Input0) = fromList transition0005Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0005 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0000 = 1 • support0481 := by
  have hs : support0000 = fromList transition0005Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0005Chunk0]
  have hn : (transition0005Raw0 : Multiset ℕ) = 1 • (supportNumbers0481 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0481] using hm

private def transition0006Input0 : List ℕ := [0, 2, 552, 554]
private def transition0006Raw0 : List ℕ := [0, 2, 296, 298]
private theorem transition0006Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0006Input0) = fromList transition0006Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0006 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0481 = 1 • support0482 := by
  have hs : support0481 = fromList transition0006Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0006Chunk0]
  have hn : (transition0006Raw0 : Multiset ℕ) = 1 • (supportNumbers0482 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0482] using hm

private def transition0007Input0 : List ℕ := [0, 2, 552, 554]
private def transition0007Raw0 : List ℕ := [0, 576, 2, 578, 296, 872, 298, 874]
private theorem transition0007Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0007Input0) = fromList transition0007Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0007 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0481 = 1 • support0483 := by
  have hs : support0481 = fromList transition0007Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0007Chunk0]
  have hn : (transition0007Raw0 : Multiset ℕ) = 1 • (supportNumbers0483 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0483] using hm

private def transition0008Input0 : List ℕ := [0, 2, 8, 10, 641, 643, 649, 651]
private def transition0008Raw0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private theorem transition0008Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0008Input0) = fromList transition0008Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0008 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0001 = 1 • support0010 := by
  have hs : support0001 = fromList transition0008Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0008Chunk0]
  have hn : (transition0008Raw0 : Multiset ℕ) = 1 • (supportNumbers0010 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0010] using hm

private def transition0009Input0 : List ℕ := [0, 2, 8, 10, 641, 643, 649, 651]
private def transition0009Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 385, 769, 387, 771, 393, 777, 395, 779]
private theorem transition0009Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0009Input0) = fromList transition0009Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0009 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0001 = 1 • support0011 := by
  have hs : support0001 = fromList transition0009Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0009Chunk0]
  have hn : (transition0009Raw0 : Multiset ℕ) = 1 • (supportNumbers0011 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0011] using hm

private def transition0010Input0 : List ℕ := [0, 2, 8, 10, 641, 643, 649, 651]
private def transition0010Raw0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private theorem transition0010Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0010Input0) = fromList transition0010Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0010 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0001 = 1 • support0010 := by
  have hs : support0001 = fromList transition0010Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0010Chunk0]
  have hn : (transition0010Raw0 : Multiset ℕ) = 1 • (supportNumbers0010 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0010] using hm

private def transition0011Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0011Raw0 : List ℕ := [0, 8, 131, 139]
private theorem transition0011Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0011Input0) = fromList transition0011Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0011 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0010 = 1 • support0485 := by
  have hs : support0010 = fromList transition0011Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0011Chunk0]
  have hn : (transition0011Raw0 : Multiset ℕ) = 1 • (supportNumbers0485 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0485] using hm

private def transition0012Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395]
private def transition0012Raw0 : List ℕ := [0, 578, 8, 586, 705, 131, 713, 139]
private theorem transition0012Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0012Input0) = fromList transition0012Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0012 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0010 = 1 • support0486 := by
  have hs : support0010 = fromList transition0012Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0012Chunk0]
  have hn : (transition0012Raw0 : Multiset ℕ) = 1 • (supportNumbers0486 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0486] using hm

private def transition0013Input0 : List ℕ := [0, 2, 8, 10, 641, 643, 649, 651]
private def transition0013Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 385, 929, 387, 931, 393, 937, 395, 939]
private theorem transition0013Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0013Input0) = fromList transition0013Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0013 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0001 = 1 • support0488 := by
  have hs : support0001 = fromList transition0013Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0013Chunk0]
  have hn : (transition0013Raw0 : Multiset ℕ) = 1 • (supportNumbers0488 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0488] using hm

private def transition0014Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 544, 546, 552, 554, 929, 931, 937, 939]
private def transition0014Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 288, 290, 296, 298, 417, 419, 425, 427]
private theorem transition0014Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0014Input0) = fromList transition0014Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0014 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0488 = 1 • support0489 := by
  have hs : support0488 = fromList transition0014Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0014Chunk0]
  have hn : (transition0014Raw0 : Multiset ℕ) = 1 • (supportNumbers0489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0489] using hm

private def transition0015Input0 : List ℕ := [0, 2, 8, 10, 385, 387, 393, 395, 544, 546, 552, 554, 929, 931, 937, 939]
private def transition0015Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 288, 864, 290, 866, 296, 872, 298, 874, 417, 993, 419, 995, 425, 1001, 427, 1003]
private theorem transition0015Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0015Input0) = fromList transition0015Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0015 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0488 = 1 • support0490 := by
  have hs : support0488 = fromList transition0015Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0015Chunk0]
  have hn : (transition0015Raw0 : Multiset ℕ) = 1 • (supportNumbers0490 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0490] using hm

private def transition0016Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition0016Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition0016Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0016Input0) = fromList transition0016Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0016 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0002 = 1 • support0012 := by
  have hs : support0002 = fromList transition0016Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0016Chunk0]
  have hn : (transition0016Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition0017Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition0017Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 660, 661, 662, 663, 28, 29, 30, 31]
private theorem transition0017Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0017Input0) = fromList transition0017Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0017 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0002 = 1 • support0013 := by
  have hs : support0002 = fromList transition0017Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0017Chunk0]
  have hn : (transition0017Raw0 : Multiset ℕ) = 1 • (supportNumbers0013 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0013] using hm

private def transition0018Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition0018Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition0018Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0018Input0) = fromList transition0018Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0018 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0002 = 1 • support0012 := by
  have hs : support0002 = fromList transition0018Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0018Chunk0]
  have hn : (transition0018Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition0019Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0019Raw0 : List ℕ := [0, 1, 28, 29]
private theorem transition0019Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0019Input0) = fromList transition0019Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0019 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0012 = 1 • support0492 := by
  have hs : support0012 = fromList transition0019Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0019Chunk0]
  have hn : (transition0019Raw0 : Multiset ℕ) = 1 • (supportNumbers0492 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0492] using hm

private def transition0020Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition0020Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607]
private theorem transition0020Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0020Input0) = fromList transition0020Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0020 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0012 = 1 • support0494 := by
  have hs : support0012 = fromList transition0020Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0020Chunk0]
  have hn : (transition0020Raw0 : Multiset ℕ) = 1 • (supportNumbers0494 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0494] using hm

private def transition0021Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition0021Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 564, 565, 566, 567, 28, 29, 30, 31]
private theorem transition0021Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0021Input0) = fromList transition0021Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0021 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0002 = 1 • support0496 := by
  have hs : support0002 = fromList transition0021Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0021Chunk0]
  have hn : (transition0021Raw0 : Multiset ℕ) = 1 • (supportNumbers0496 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0496] using hm

private def transition0022Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 552, 553, 554, 555, 564, 565, 566, 567]
private def transition0022Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 296, 297, 298, 299, 308, 309, 310, 311]
private theorem transition0022Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0022Input0) = fromList transition0022Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0022 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0496 = 1 • support0497 := by
  have hs : support0496 = fromList transition0022Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0022Chunk0]
  have hn : (transition0022Raw0 : Multiset ℕ) = 1 • (supportNumbers0497 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0497] using hm

private def transition0023Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 552, 553, 554, 555, 564, 565, 566, 567]
private def transition0023Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887]
private theorem transition0023Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0023Input0) = fromList transition0023Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0023 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0496 = 1 • support0499 := by
  have hs : support0496 = fromList transition0023Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0023Chunk0]
  have hn : (transition0023Raw0 : Multiset ℕ) = 1 • (supportNumbers0499 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0499] using hm

private def transition0024Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0024Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0024Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0024Input0) = fromList transition0024Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0024 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0003 = 1 • support0014 := by
  have hs : support0003 = fromList transition0024Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0024Chunk0]
  have hn : (transition0024Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition0025Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0025Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0025Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0025Input0) = fromList transition0025Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0025 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0003 = 1 • support0015 := by
  have hs : support0003 = fromList transition0025Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0025Chunk0]
  have hn : (transition0025Raw0 : Multiset ℕ) = 1 • (supportNumbers0015 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0015] using hm

private def transition0026Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0026Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0026Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0026Input0) = fromList transition0026Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0026 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0003 = 1 • support0014 := by
  have hs : support0003 = fromList transition0026Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0026Chunk0]
  have hn : (transition0026Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition0027Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0027Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 130, 131, 138, 139, 150, 151, 158, 159]
private theorem transition0027Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0027Input0) = fromList transition0027Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0027 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0014 = 1 • support0501 := by
  have hs : support0014 = fromList transition0027Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0027Chunk0]
  have hn : (transition0027Raw0 : Multiset ℕ) = 1 • (supportNumbers0501 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0501] using hm

private def transition0028Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0028Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 20, 21, 598, 599, 28, 29, 606, 607, 704, 705, 130, 131, 712, 713, 138, 139, 724, 725, 150, 151, 732, 733, 158, 159]
private theorem transition0028Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0028Input0) = fromList transition0028Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0028 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0014 = 1 • support0503 := by
  have hs : support0014 = fromList transition0028Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0028Chunk0]
  have hn : (transition0028Raw0 : Multiset ℕ) = 1 • (supportNumbers0503 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0503] using hm

private def transition0029Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0029Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0029Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0029Input0) = fromList transition0029Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0029 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0003 = 1 • support0505 := by
  have hs : support0003 = fromList transition0029Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0029Chunk0]
  have hn : (transition0029Raw0 : Multiset ℕ) = 1 • (supportNumbers0505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0505] using hm

private def transition0030Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 928, 929, 930, 931, 936, 937, 938, 939, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0030Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition0030Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0030Input0) = fromList transition0030Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0030 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0505 = 1 • support0506 := by
  have hs : support0505 = fromList transition0030Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0030Chunk0]
  have hn : (transition0030Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm

private def transition0031Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 928, 929, 930, 931, 936, 937, 938, 939, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0031Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0031Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0031Input0) = fromList transition0031Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0031 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0505 = 1 • support0508 := by
  have hs : support0505 = fromList transition0031Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0031Chunk0]
  have hn : (transition0031Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0032Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0032Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0032Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0032Input0) = fromList transition0032Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0032 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0004 = 1 • support0016 := by
  have hs : support0004 = fromList transition0032Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0032Chunk0]
  have hn : (transition0032Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0033Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0033Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719]
private theorem transition0033Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0033Input0) = fromList transition0033Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0033 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0004 = 1 • support0017 := by
  have hs : support0004 = fromList transition0033Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0033Chunk0]
  have hn : (transition0033Raw0 : Multiset ℕ) = 1 • (supportNumbers0017 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0017] using hm

private def transition0034Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0034Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0034Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0034Input0) = fromList transition0034Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0034 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0004 = 1 • support0016 := by
  have hs : support0004 = fromList transition0034Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0034Chunk0]
  have hn : (transition0034Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0035Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0035Raw0 : List ℕ := [0, 4, 65, 69]
private theorem transition0035Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0035Input0) = fromList transition0035Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0035 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0016 = 1 • support0510 := by
  have hs : support0016 = fromList transition0035Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0035Chunk0]
  have hn : (transition0035Raw0 : Multiset ℕ) = 1 • (supportNumbers0510 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0510] using hm

private def transition0036Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0036Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519]
private theorem transition0036Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0036Input0) = fromList transition0036Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0036 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0016 = 1 • support0512 := by
  have hs : support0016 = fromList transition0036Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0036Chunk0]
  have hn : (transition0036Raw0 : Multiset ℕ) = 1 • (supportNumbers0512 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0512] using hm

private def transition0037Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0037Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623]
private theorem transition0037Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0037Input0) = fromList transition0037Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0037 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0004 = 1 • support0514 := by
  have hs : support0004 = fromList transition0037Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0037Chunk0]
  have hn : (transition0037Raw0 : Multiset ℕ) = 1 • (supportNumbers0514 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0514] using hm

private def transition0038Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 552, 554, 556, 558, 617, 619, 621, 623]
private def transition0038Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 296, 298, 300, 302, 361, 363, 365, 367]
private theorem transition0038Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0038Input0) = fromList transition0038Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0038 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0514 = 1 • support0515 := by
  have hs : support0514 = fromList transition0038Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0038Chunk0]
  have hn : (transition0038Raw0 : Multiset ℕ) = 1 • (supportNumbers0515 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0515] using hm

private def transition0039Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 552, 554, 556, 558, 617, 619, 621, 623]
private def transition0039Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815]
private theorem transition0039Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0039Input0) = fromList transition0039Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0039 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0514 = 1 • support0517 := by
  have hs : support0514 = fromList transition0039Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0039Chunk0]
  have hn : (transition0039Raw0 : Multiset ℕ) = 1 • (supportNumbers0517 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0517] using hm

private def transition0040Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition0040Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition0040Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0040Input0) = fromList transition0040Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0040 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0005 = 1 • support0018 := by
  have hs : support0005 = fromList transition0040Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0040Chunk0]
  have hn : (transition0040Raw0 : Multiset ℕ) = 1 • (supportNumbers0018 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0018] using hm

private def transition0041Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition0041Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 385, 769, 387, 771, 389, 773, 391, 775, 393, 777, 395, 779, 397, 781, 399, 783, 448, 832, 450, 834, 452, 836, 454, 838, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition0041Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0041Input0) = fromList transition0041Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0041 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0005 = 1 • support0019 := by
  have hs : support0005 = fromList transition0041Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0041Chunk0]
  have hn : (transition0041Raw0 : Multiset ℕ) = 1 • (supportNumbers0019 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0019] using hm

private def transition0042Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition0042Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private theorem transition0042Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0042Input0) = fromList transition0042Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0042 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0005 = 1 • support0018 := by
  have hs : support0005 = fromList transition0042Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0042Chunk0]
  have hn : (transition0042Raw0 : Multiset ℕ) = 1 • (supportNumbers0018 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0018] using hm

private def transition0043Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0043Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 131, 135, 139, 143, 194, 198, 202, 206]
private theorem transition0043Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0043Input0) = fromList transition0043Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0043 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0018 = 1 • support0519 := by
  have hs : support0018 = fromList transition0043Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0043Chunk0]
  have hn : (transition0043Raw0 : Multiset ℕ) = 1 • (supportNumbers0519 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0519] using hm

private def transition0044Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462]
private def transition0044Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 705, 131, 709, 135, 713, 139, 717, 143, 640, 194, 644, 198, 648, 202, 652, 206]
private theorem transition0044Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0044Input0) = fromList transition0044Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0044 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0018 = 1 • support0521 := by
  have hs : support0018 = fromList transition0044Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0044Chunk0]
  have hn : (transition0044Raw0 : Multiset ℕ) = 1 • (supportNumbers0521 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0521] using hm

private def transition0045Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def transition0045Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 8, 552, 10, 554, 12, 556, 14, 558, 65, 609, 67, 611, 69, 613, 71, 615, 73, 617, 75, 619, 77, 621, 79, 623, 385, 929, 387, 931, 389, 933, 391, 935, 393, 937, 395, 939, 397, 941, 399, 943, 448, 992, 450, 994, 452, 996, 454, 998, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition0045Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0045Input0) = fromList transition0045Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0045 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0005 = 1 • support0523 := by
  have hs : support0005 = fromList transition0045Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0045Chunk0]
  have hn : (transition0045Raw0 : Multiset ℕ) = 1 • (supportNumbers0523 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0523] using hm

private def transition0046Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 385, 387, 389, 391, 393, 395, 397, 399, 448, 450, 452, 454, 456, 458, 460, 462, 544, 546, 548, 550, 552, 554, 556, 558, 609, 611, 613, 615, 617, 619, 621, 623, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def transition0046Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206, 288, 290, 292, 294, 296, 298, 300, 302, 353, 355, 357, 359, 361, 363, 365, 367, 417, 419, 421, 423, 425, 427, 429, 431, 480, 482, 484, 486, 488, 490, 492, 494]
private theorem transition0046Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0046Input0) = fromList transition0046Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0046 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0523 = 1 • support0524 := by
  have hs : support0523 = fromList transition0046Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0046Chunk0]
  have hn : (transition0046Raw0 : Multiset ℕ) = 1 • (supportNumbers0524 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0524] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
