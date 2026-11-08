import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0811Input0 : List ℕ := [0, 2, 265, 267, 640, 642, 905, 907]
private def transition0811Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition0811Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0811Input0) = fromList transition0811Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0811 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0106 = 1 • support0177 := by
  have hs : support0106 = fromList transition0811Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0811Chunk0]
  have hn : (transition0811Raw0 : Multiset ℕ) = 1 • (supportNumbers0177 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0177] using hm

private def transition0812Input0 : List ℕ := [0, 2, 265, 267, 640, 642, 905, 907]
private def transition0812Raw0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private theorem transition0812Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0812Input0) = fromList transition0812Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0812 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0106 = 1 • support0176 := by
  have hs : support0106 = fromList transition0812Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0812Chunk0]
  have hn : (transition0812Raw0 : Multiset ℕ) = 1 • (supportNumbers0176 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0176] using hm

private def transition0813Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition0813Raw0 : List ℕ := [0, 9, 130, 139]
private theorem transition0813Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0813Input0) = fromList transition0813Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0813 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0176 = 1 • support1044 := by
  have hs : support0176 = fromList transition0813Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0813Chunk0]
  have hn : (transition0813Raw0 : Multiset ℕ) = 1 • (supportNumbers1044 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1044] using hm

private def transition0814Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private def transition0814Raw0 : List ℕ := [0, 578, 9, 587, 704, 130, 713, 139]
private theorem transition0814Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0814Input0) = fromList transition0814Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0814 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0176 = 1 • support1045 := by
  have hs : support0176 = fromList transition0814Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0814Chunk0]
  have hn : (transition0814Raw0 : Multiset ℕ) = 1 • (supportNumbers1045 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1045] using hm

private def transition0815Input0 : List ℕ := [0, 2, 265, 267, 640, 642, 905, 907]
private def transition0815Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition0815Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0815Input0) = fromList transition0815Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0815 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0106 = 1 • support1047 := by
  have hs : support0106 = fromList transition0815Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0815Chunk0]
  have hn : (transition0815Raw0 : Multiset ℕ) = 1 • (supportNumbers1047 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1047] using hm

private def transition0816Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 544, 546, 553, 555, 928, 930, 937, 939]
private def transition0816Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 288, 290, 297, 299, 416, 418, 425, 427]
private theorem transition0816Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0816Input0) = fromList transition0816Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0816 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1047 = 1 • support1048 := by
  have hs : support1047 = fromList transition0816Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0816Chunk0]
  have hn : (transition0816Raw0 : Multiset ℕ) = 1 • (supportNumbers1048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1048] using hm

private def transition0817Input0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395, 544, 546, 553, 555, 928, 930, 937, 939]
private def transition0817Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 128, 704, 130, 706, 137, 713, 139, 715, 288, 864, 290, 866, 297, 873, 299, 875, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition0817Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0817Input0) = fromList transition0817Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0817 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1047 = 1 • support1049 := by
  have hs : support1047 = fromList transition0817Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0817Chunk0]
  have hn : (transition0817Raw0 : Multiset ℕ) = 1 • (supportNumbers1049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1049] using hm

private def transition0818Input0 : List ℕ := [0, 2, 136, 138, 521, 523, 641, 643]
private def transition0818Raw0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private theorem transition0818Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0818Input0) = fromList transition0818Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0818 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0107 = 1 • support0178 := by
  have hs : support0107 = fromList transition0818Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0818Chunk0]
  have hn : (transition0818Raw0 : Multiset ℕ) = 1 • (supportNumbers0178 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0178] using hm

private def transition0819Input0 : List ℕ := [0, 2, 136, 138, 521, 523, 641, 643]
private def transition0819Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 265, 905, 267, 907, 385, 769, 387, 771]
private theorem transition0819Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0819Input0) = fromList transition0819Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0819 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0107 = 1 • support0179 := by
  have hs : support0107 = fromList transition0819Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0819Chunk0]
  have hn : (transition0819Raw0 : Multiset ℕ) = 1 • (supportNumbers0179 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0179] using hm

private def transition0820Input0 : List ℕ := [0, 2, 136, 138, 521, 523, 641, 643]
private def transition0820Raw0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private theorem transition0820Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0820Input0) = fromList transition0820Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0820 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0107 = 1 • support0178 := by
  have hs : support0107 = fromList transition0820Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0820Chunk0]
  have hn : (transition0820Raw0 : Multiset ℕ) = 1 • (supportNumbers0178 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0178] using hm

private def transition0821Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition0821Raw0 : List ℕ := [0, 136, 11, 131]
private theorem transition0821Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0821Input0) = fromList transition0821Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0821 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0178 = 1 • support1051 := by
  have hs : support0178 = fromList transition0821Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0821Chunk0]
  have hn : (transition0821Raw0 : Multiset ℕ) = 1 • (supportNumbers1051 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1051] using hm

private def transition0822Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387]
private def transition0822Raw0 : List ℕ := [0, 578, 136, 714, 585, 11, 705, 131]
private theorem transition0822Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0822Input0) = fromList transition0822Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0822 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0178 = 1 • support1052 := by
  have hs : support0178 = fromList transition0822Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0822Chunk0]
  have hn : (transition0822Raw0 : Multiset ℕ) = 1 • (supportNumbers1052 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1052] using hm

private def transition0823Input0 : List ℕ := [0, 2, 136, 138, 521, 523, 641, 643]
private def transition0823Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 265, 809, 267, 811, 385, 929, 387, 931]
private theorem transition0823Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0823Input0) = fromList transition0823Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0823 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0107 = 1 • support1054 := by
  have hs : support0107 = fromList transition0823Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0823Chunk0]
  have hn : (transition0823Raw0 : Multiset ℕ) = 1 • (supportNumbers1054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1054] using hm

private def transition0824Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 544, 546, 680, 682, 809, 811, 929, 931]
private def transition0824Raw0 : List ℕ := [0, 2, 136, 138, 9, 11, 129, 131, 288, 290, 424, 426, 297, 299, 417, 419]
private theorem transition0824Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0824Input0) = fromList transition0824Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0824 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1054 = 1 • support0841 := by
  have hs : support1054 = fromList transition0824Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0824Chunk0]
  have hn : (transition0824Raw0 : Multiset ℕ) = 1 • (supportNumbers0841 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0841] using hm

private def transition0825Input0 : List ℕ := [0, 2, 136, 138, 265, 267, 385, 387, 544, 546, 680, 682, 809, 811, 929, 931]
private def transition0825Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 9, 585, 11, 587, 129, 705, 131, 707, 288, 864, 290, 866, 424, 1000, 426, 1002, 297, 873, 299, 875, 417, 993, 419, 995]
private theorem transition0825Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0825Input0) = fromList transition0825Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0825 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1054 = 1 • support0842 := by
  have hs : support1054 = fromList transition0825Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0825Chunk0]
  have hn : (transition0825Raw0 : Multiset ℕ) = 1 • (supportNumbers0842 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0842] using hm

private def transition0826Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0826Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition0826Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0826Input0) = fromList transition0826Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0826 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0108 = 1 • support0180 := by
  have hs : support0108 = fromList transition0826Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0826Chunk0]
  have hn : (transition0826Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition0827Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0827Raw0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523, 8, 9, 10, 11, 512, 513, 514, 515]
private theorem transition0827Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0827Input0) = fromList transition0827Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0827 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0108 = 1 • support0181 := by
  have hs : support0108 = fromList transition0827Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0827Chunk0]
  have hn : (transition0827Raw0 : Multiset ℕ) = 1 • (supportNumbers0181 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0181] using hm

private def transition0828Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0828Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition0828Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0828Input0) = fromList transition0828Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0828 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0108 = 1 • support0180 := by
  have hs : support0108 = fromList transition0828Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0828Chunk0]
  have hn : (transition0828Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition0829Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition0829Raw0 : List ℕ := [0, 1, 8, 9]
private theorem transition0829Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0829Input0) = fromList transition0829Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0829 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0180 = 1 • support0874 := by
  have hs : support0180 = fromList transition0829Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0829Chunk0]
  have hn : (transition0829Raw0 : Multiset ℕ) = 1 • (supportNumbers0874 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0874] using hm

private def transition0830Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition0830Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587]
private theorem transition0830Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0830Input0) = fromList transition0830Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0830 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0180 = 1 • support1055 := by
  have hs : support0180 = fromList transition0830Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0830Chunk0]
  have hn : (transition0830Raw0 : Multiset ℕ) = 1 • (supportNumbers1055 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1055] using hm

private def transition0831Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0831Raw0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683, 8, 9, 10, 11, 672, 673, 674, 675]
private theorem transition0831Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0831Input0) = fromList transition0831Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0831 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0108 = 1 • support1057 := by
  have hs : support0108 = fromList transition0831Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0831Chunk0]
  have hn : (transition0831Raw0 : Multiset ℕ) = 1 • (supportNumbers1057 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1057] using hm

private def transition0832Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0832Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition0832Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0832Input0) = fromList transition0832Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0832 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1057 = 1 • support1058 := by
  have hs : support1057 = fromList transition0832Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0832Chunk0]
  have hn : (transition0832Raw0 : Multiset ℕ) = 1 • (supportNumbers1058 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1058] using hm

private def transition0833Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0833Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0833Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0833Input0) = fromList transition0833Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0833 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1057 = 1 • support1059 := by
  have hs : support1057 = fromList transition0833Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0833Chunk0]
  have hn : (transition0833Raw0 : Multiset ℕ) = 1 • (supportNumbers1059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1059] using hm

private def transition0834Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 520, 521, 522, 523, 640, 641, 642, 643, 768, 769, 770, 771, 904, 905, 906, 907]
private def transition0834Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 8, 9, 10, 11, 128, 129, 130, 131, 264, 265, 266, 267, 384, 385, 386, 387, 256, 257, 258, 259, 392, 393, 394, 395]
private theorem transition0834Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0834Input0) = fromList transition0834Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0834 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0109 = 1 • support0061 := by
  have hs : support0109 = fromList transition0834Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0834Chunk0]
  have hn : (transition0834Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0835Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 520, 521, 522, 523, 640, 641, 642, 643, 768, 769, 770, 771, 904, 905, 906, 907]
private def transition0835Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 256, 896, 257, 897, 258, 898, 259, 899, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition0835Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0835Input0) = fromList transition0835Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0835 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0109 = 1 • support0062 := by
  have hs : support0109 = fromList transition0835Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0835Chunk0]
  have hn : (transition0835Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition0836Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 520, 521, 522, 523, 640, 641, 642, 643, 768, 769, 770, 771, 904, 905, 906, 907]
private def transition0836Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 8, 9, 10, 11, 128, 129, 130, 131, 264, 265, 266, 267, 384, 385, 386, 387, 256, 257, 258, 259, 392, 393, 394, 395]
private theorem transition0836Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0836Input0) = fromList transition0836Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0836 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0109 = 1 • support0061 := by
  have hs : support0109 = fromList transition0836Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0836Chunk0]
  have hn : (transition0836Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0837Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 520, 521, 522, 523, 640, 641, 642, 643, 768, 769, 770, 771, 904, 905, 906, 907]
private def transition0837Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 256, 800, 257, 801, 258, 802, 259, 803, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition0837Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0837Input0) = fromList transition0837Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0837 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0109 = 1 • support0680 := by
  have hs : support0109 = fromList transition0837Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0837Chunk0]
  have hn : (transition0837Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition0838Input0 : List ℕ := [0, 2, 129, 131]
private def transition0838Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0838Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0838Input0) = fromList transition0838Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0838 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition0838Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0838Chunk0]
  have hn : (transition0838Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0839Input0 : List ℕ := [0, 2, 129, 131]
private def transition0839Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0839Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0839Input0) = fromList transition0839Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0839 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition0839Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0839Chunk0]
  have hn : (transition0839Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0840Input0 : List ℕ := [0, 2, 129, 131]
private def transition0840Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0840Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0840Input0) = fromList transition0840Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0840 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition0840Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0840Chunk0]
  have hn : (transition0840Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0841Input0 : List ℕ := [0, 2, 129, 131]
private def transition0841Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0841Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0841Input0) = fromList transition0841Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0841 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition0841Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0841Chunk0]
  have hn : (transition0841Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0842Input0 : List ℕ := [0, 2, 129, 131]
private def transition0842Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0842Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0842Input0) = fromList transition0842Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0842 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0110 = 1 • support0110 := by
  have hs : support0110 = fromList transition0842Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0842Chunk0]
  have hn : (transition0842Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0843Input0 : List ℕ := [0, 2, 129, 131]
private def transition0843Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707]
private theorem transition0843Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0843Input0) = fromList transition0843Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0843 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0110 = 1 • support1061 := by
  have hs : support0110 = fromList transition0843Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0843Chunk0]
  have hn : (transition0843Raw0 : Multiset ℕ) = 1 • (supportNumbers1061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1061] using hm

private def transition0844Input0 : List ℕ := [0, 2, 129, 131, 520, 522, 649, 651]
private def transition0844Raw0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private theorem transition0844Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0844Input0) = fromList transition0844Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0844 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0111 = 1 • support0182 := by
  have hs : support0111 = fromList transition0844Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0844Chunk0]
  have hn : (transition0844Raw0 : Multiset ℕ) = 1 • (supportNumbers0182 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0182] using hm

private def transition0845Input0 : List ℕ := [0, 2, 129, 131, 520, 522, 649, 651]
private def transition0845Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 264, 904, 266, 906, 393, 777, 395, 779]
private theorem transition0845Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0845Input0) = fromList transition0845Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0845 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0111 = 1 • support0183 := by
  have hs : support0111 = fromList transition0845Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0845Chunk0]
  have hn : (transition0845Raw0 : Multiset ℕ) = 1 • (supportNumbers0183 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0183] using hm

private def transition0846Input0 : List ℕ := [0, 2, 129, 131, 520, 522, 649, 651]
private def transition0846Raw0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private theorem transition0846Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0846Input0) = fromList transition0846Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0846 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0111 = 1 • support0182 := by
  have hs : support0111 = fromList transition0846Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0846Chunk0]
  have hn : (transition0846Raw0 : Multiset ℕ) = 1 • (supportNumbers0182 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0182] using hm

private def transition0847Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition0847Raw0 : List ℕ := [0, 129, 10, 139]
private theorem transition0847Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0847Input0) = fromList transition0847Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0847 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0182 = 1 • support1063 := by
  have hs : support0182 = fromList transition0847Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0847Chunk0]
  have hn : (transition0847Raw0 : Multiset ℕ) = 1 • (supportNumbers1063 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1063] using hm

private def transition0848Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395]
private def transition0848Raw0 : List ℕ := [0, 578, 129, 707, 584, 10, 713, 139]
private theorem transition0848Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0848Input0) = fromList transition0848Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0848 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0182 = 1 • support1064 := by
  have hs : support0182 = fromList transition0848Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0848Chunk0]
  have hn : (transition0848Raw0 : Multiset ℕ) = 1 • (supportNumbers1064 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1064] using hm

private def transition0849Input0 : List ℕ := [0, 2, 129, 131, 520, 522, 649, 651]
private def transition0849Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 264, 808, 266, 810, 393, 937, 395, 939]
private theorem transition0849Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0849Input0) = fromList transition0849Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0849 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0111 = 1 • support1066 := by
  have hs : support0111 = fromList transition0849Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0849Chunk0]
  have hn : (transition0849Raw0 : Multiset ℕ) = 1 • (supportNumbers1066 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1066] using hm

private def transition0850Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 544, 546, 673, 675, 808, 810, 937, 939]
private def transition0850Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139, 288, 290, 417, 419, 296, 298, 425, 427]
private theorem transition0850Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0850Input0) = fromList transition0850Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0850 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1066 = 1 • support0489 := by
  have hs : support1066 = fromList transition0850Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0850Chunk0]
  have hn : (transition0850Raw0 : Multiset ℕ) = 1 • (supportNumbers0489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0489] using hm

private def transition0851Input0 : List ℕ := [0, 2, 129, 131, 264, 266, 393, 395, 544, 546, 673, 675, 808, 810, 937, 939]
private def transition0851Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 8, 584, 10, 586, 137, 713, 139, 715, 288, 864, 290, 866, 417, 993, 419, 995, 296, 872, 298, 874, 425, 1001, 427, 1003]
private theorem transition0851Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0851Input0) = fromList transition0851Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0851 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1066 = 1 • support0490 := by
  have hs : support1066 = fromList transition0851Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0851Chunk0]
  have hn : (transition0851Raw0 : Multiset ℕ) = 1 • (supportNumbers0490 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0490] using hm

private def transition0852Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0852Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition0852Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0852Input0) = fromList transition0852Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0852 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0112 = 1 • support0059 := by
  have hs : support0112 = fromList transition0852Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0852Chunk0]
  have hn : (transition0852Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition0853Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0853Raw0 : List ℕ := [0, 2, 649, 651, 129, 131, 520, 522, 640, 642, 9, 11, 513, 515, 136, 138]
private theorem transition0853Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0853Input0) = fromList transition0853Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0853 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0112 = 1 • support0184 := by
  have hs : support0112 = fromList transition0853Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0853Chunk0]
  have hn : (transition0853Raw0 : Multiset ℕ) = 1 • (supportNumbers0184 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0184] using hm

private def transition0854Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0854Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition0854Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0854Input0) = fromList transition0854Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0854 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0112 = 1 • support0059 := by
  have hs : support0112 = fromList transition0854Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0854Chunk0]
  have hn : (transition0854Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition0855Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0855Raw0 : List ℕ := [0, 2, 553, 555, 129, 131, 680, 682, 544, 546, 9, 11, 673, 675, 136, 138]
private theorem transition0855Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0855Input0) = fromList transition0855Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0855 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0112 = 1 • support1067 := by
  have hs : support0112 = fromList transition0855Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0855Chunk0]
  have hn : (transition0855Raw0 : Multiset ℕ) = 1 • (supportNumbers1067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1067] using hm

private def transition0856Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 544, 546, 553, 555, 673, 675, 680, 682]
private def transition0856Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 288, 290, 297, 299, 417, 419, 424, 426]
private theorem transition0856Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0856Input0) = fromList transition0856Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0856 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1067 = 1 • support0841 := by
  have hs : support1067 = fromList transition0856Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0856Chunk0]
  have hn : (transition0856Raw0 : Multiset ℕ) = 1 • (supportNumbers0841 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0841] using hm

private def transition0857Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 544, 546, 553, 555, 673, 675, 680, 682]
private def transition0857Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714, 288, 864, 290, 866, 297, 873, 299, 875, 417, 993, 419, 995, 424, 1000, 426, 1002]
private theorem transition0857Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0857Input0) = fromList transition0857Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0857 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1067 = 1 • support0842 := by
  have hs : support1067 = fromList transition0857Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0857Chunk0]
  have hn : (transition0857Raw0 : Multiset ℕ) = 1 • (supportNumbers0842 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0842] using hm

private def transition0858Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 513, 515, 520, 522, 640, 642, 649, 651, 769, 771, 776, 778, 896, 898, 905, 907]
private def transition0858Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 257, 259, 264, 266, 384, 386, 393, 395]
private theorem transition0858Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0858Input0) = fromList transition0858Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0858 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0113 = 2 • support0185 := by
  have hs : support0113 = fromList transition0858Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0858Chunk0]
  have hn : (transition0858Raw0 : Multiset ℕ) = 2 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition0859Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 513, 515, 520, 522, 640, 642, 649, 651, 769, 771, 776, 778, 896, 898, 905, 907]
private def transition0859Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 129, 513, 131, 515, 136, 520, 138, 522, 0, 640, 2, 642, 9, 649, 11, 651, 129, 513, 131, 515, 136, 520, 138, 522, 257, 897, 259, 899, 264, 904, 266, 906, 384, 768, 386, 770, 393, 777, 395, 779, 257, 897, 259, 899, 264, 904, 266, 906, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition0859Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0859Input0) = fromList transition0859Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0859 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0113 = 2 • support0186 := by
  have hs : support0113 = fromList transition0859Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0859Chunk0]
  have hn : (transition0859Raw0 : Multiset ℕ) = 2 • (supportNumbers0186 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0186] using hm

private def transition0860Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 513, 515, 520, 522, 640, 642, 649, 651, 769, 771, 776, 778, 896, 898, 905, 907]
private def transition0860Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 257, 259, 264, 266, 384, 386, 393, 395]
private theorem transition0860Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0860Input0) = fromList transition0860Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0860 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0113 = 2 • support0185 := by
  have hs : support0113 = fromList transition0860Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0860Chunk0]
  have hn : (transition0860Raw0 : Multiset ℕ) = 2 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition0861Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition0861Raw0 : List ℕ := [0, 9, 129, 136, 3, 10, 130, 139]
private theorem transition0861Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0861Input0) = fromList transition0861Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0861 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0185 = 1 • support1068 := by
  have hs : support0185 = fromList transition0861Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0861Chunk0]
  have hn : (transition0861Raw0 : Multiset ℕ) = 1 • (supportNumbers1068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1068] using hm

private def transition0862Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395]
private def transition0862Raw0 : List ℕ := [0, 578, 9, 587, 129, 707, 136, 714, 577, 3, 584, 10, 704, 130, 713, 139]
private theorem transition0862Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0862Input0) = fromList transition0862Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0862 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0185 = 1 • support1069 := by
  have hs : support0185 = fromList transition0862Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0862Chunk0]
  have hn : (transition0862Raw0 : Multiset ℕ) = 1 • (supportNumbers1069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1069] using hm

private def transition0863Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 513, 515, 520, 522, 640, 642, 649, 651, 769, 771, 776, 778, 896, 898, 905, 907]
private def transition0863Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 129, 673, 131, 675, 136, 680, 138, 682, 0, 544, 2, 546, 9, 553, 11, 555, 129, 673, 131, 675, 136, 680, 138, 682, 257, 801, 259, 803, 264, 808, 266, 810, 384, 928, 386, 930, 393, 937, 395, 939, 257, 801, 259, 803, 264, 808, 266, 810, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition0863Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0863Input0) = fromList transition0863Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0863 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0113 = 2 • support1071 := by
  have hs : support0113 = fromList transition0863Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0863Chunk0]
  have hn : (transition0863Raw0 : Multiset ℕ) = 2 • (supportNumbers1071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1071] using hm

private def transition0864Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 544, 546, 553, 555, 673, 675, 680, 682, 801, 803, 808, 810, 928, 930, 937, 939]
private def transition0864Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 1, 3, 8, 10, 128, 130, 137, 139, 288, 290, 297, 299, 417, 419, 424, 426, 289, 291, 296, 298, 416, 418, 425, 427]
private theorem transition0864Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0864Input0) = fromList transition0864Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0864 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1071 = 1 • support0564 := by
  have hs : support1071 = fromList transition0864Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0864Chunk0]
  have hn : (transition0864Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition0865Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 257, 259, 264, 266, 384, 386, 393, 395, 544, 546, 553, 555, 673, 675, 680, 682, 801, 803, 808, 810, 928, 930, 937, 939]
private def transition0865Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714, 1, 577, 3, 579, 8, 584, 10, 586, 128, 704, 130, 706, 137, 713, 139, 715, 288, 864, 290, 866, 297, 873, 299, 875, 417, 993, 419, 995, 424, 1000, 426, 1002, 289, 865, 291, 867, 296, 872, 298, 874, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition0865Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0865Input0) = fromList transition0865Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0865 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1071 = 1 • support0565 := by
  have hs : support1071 = fromList transition0865Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0865Chunk0]
  have hn : (transition0865Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition0866Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0866Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition0866Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0866Input0) = fromList transition0866Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0866 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0114 = 1 • support0187 := by
  have hs : support0114 = fromList transition0866Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0866Chunk0]
  have hn : (transition0866Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition0867Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0867Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 128, 129, 130, 131, 520, 521, 522, 523]
private theorem transition0867Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0867Input0) = fromList transition0867Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0867 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0114 = 1 • support0188 := by
  have hs : support0114 = fromList transition0867Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0867Chunk0]
  have hn : (transition0867Raw0 : Multiset ℕ) = 1 • (supportNumbers0188 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0188] using hm

private def transition0868Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0868Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition0868Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0868Input0) = fromList transition0868Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0868 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0114 = 1 • support0187 := by
  have hs : support0114 = fromList transition0868Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0868Chunk0]
  have hn : (transition0868Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition0869Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition0869Raw0 : List ℕ := [0, 1, 128, 129]
private theorem transition0869Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0869Input0) = fromList transition0869Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0869 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0187 = 1 • support0898 := by
  have hs : support0187 = fromList transition0869Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0869Chunk0]
  have hn : (transition0869Raw0 : Multiset ℕ) = 1 • (supportNumbers0898 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0898] using hm

private def transition0870Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition0870Raw0 : List ℕ := [0, 1, 578, 579, 128, 129, 706, 707]
private theorem transition0870Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0870Input0) = fromList transition0870Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0870 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0187 = 1 • support1072 := by
  have hs : support0187 = fromList transition0870Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0870Chunk0]
  have hn : (transition0870Raw0 : Multiset ℕ) = 1 • (supportNumbers1072 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1072] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
