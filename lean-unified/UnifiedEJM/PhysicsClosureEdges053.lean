import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0871Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0871Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 128, 129, 130, 131, 680, 681, 682, 683]
private theorem transition0871Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0871Input0) = fromList transition0871Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0871 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0114 = 1 • support1074 := by
  have hs : support0114 = fromList transition0871Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0871Chunk0]
  have hn : (transition0871Raw0 : Multiset ℕ) = 1 • (supportNumbers1074 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1074] using hm

private def transition0872Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 552, 553, 554, 555, 680, 681, 682, 683]
private def transition0872Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 296, 297, 298, 299, 424, 425, 426, 427]
private theorem transition0872Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0872Input0) = fromList transition0872Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0872 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1074 = 1 • support1075 := by
  have hs : support1074 = fromList transition0872Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0872Chunk0]
  have hn : (transition0872Raw0 : Multiset ℕ) = 1 • (supportNumbers1075 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1075] using hm

private def transition0873Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 552, 553, 554, 555, 680, 681, 682, 683]
private def transition0873Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 296, 872, 297, 873, 298, 874, 299, 875, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0873Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0873Input0) = fromList transition0873Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0873 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1074 = 1 • support1076 := by
  have hs : support1074 = fromList transition0873Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0873Chunk0]
  have hn : (transition0873Raw0 : Multiset ℕ) = 1 • (supportNumbers1076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1076] using hm

private def transition0874Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition0874Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition0874Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0874Input0) = fromList transition0874Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0874 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0115 = 1 • support0061 := by
  have hs : support0115 = fromList transition0874Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0874Chunk0]
  have hn : (transition0874Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0875Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition0875Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition0875Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0875Input0) = fromList transition0875Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0875 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0115 = 1 • support0062 := by
  have hs : support0115 = fromList transition0875Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0875Chunk0]
  have hn : (transition0875Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition0876Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition0876Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition0876Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0876Input0) = fromList transition0876Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0876 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0115 = 1 • support0061 := by
  have hs : support0115 = fromList transition0876Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0876Chunk0]
  have hn : (transition0876Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0877Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition0877Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition0877Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0877Input0) = fromList transition0877Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0877 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0115 = 1 • support0680 := by
  have hs : support0115 = fromList transition0877Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0877Chunk0]
  have hn : (transition0877Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition0878Input0 : List ℕ := [0, 1, 2, 3, 640, 641, 642, 643]
private def transition0878Raw0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private theorem transition0878Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0878Input0) = fromList transition0878Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0878 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0116 = 1 • support0189 := by
  have hs : support0116 = fromList transition0878Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0878Chunk0]
  have hn : (transition0878Raw0 : Multiset ℕ) = 1 • (supportNumbers0189 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0189] using hm

private def transition0879Input0 : List ℕ := [0, 1, 2, 3, 640, 641, 642, 643]
private def transition0879Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition0879Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0879Input0) = fromList transition0879Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0879 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0116 = 1 • support0190 := by
  have hs : support0116 = fromList transition0879Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0879Chunk0]
  have hn : (transition0879Raw0 : Multiset ℕ) = 1 • (supportNumbers0190 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0190] using hm

private def transition0880Input0 : List ℕ := [0, 1, 2, 3, 640, 641, 642, 643]
private def transition0880Raw0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private theorem transition0880Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0880Input0) = fromList transition0880Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0880 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0116 = 1 • support0189 := by
  have hs : support0116 = fromList transition0880Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0880Chunk0]
  have hn : (transition0880Raw0 : Multiset ℕ) = 1 • (supportNumbers0189 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0189] using hm

private def transition0881Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition0881Raw0 : List ℕ := [0, 1, 130, 131]
private theorem transition0881Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0881Input0) = fromList transition0881Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0881 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0189 = 1 • support0857 := by
  have hs : support0189 = fromList transition0881Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0881Chunk0]
  have hn : (transition0881Raw0 : Multiset ℕ) = 1 • (supportNumbers0857 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0857] using hm

private def transition0882Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387]
private def transition0882Raw0 : List ℕ := [0, 1, 578, 579, 704, 705, 130, 131]
private theorem transition0882Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0882Input0) = fromList transition0882Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0882 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0189 = 1 • support1078 := by
  have hs : support0189 = fromList transition0882Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0882Chunk0]
  have hn : (transition0882Raw0 : Multiset ℕ) = 1 • (supportNumbers1078 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1078] using hm

private def transition0883Input0 : List ℕ := [0, 1, 2, 3, 640, 641, 642, 643]
private def transition0883Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition0883Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0883Input0) = fromList transition0883Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0883 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0116 = 1 • support1080 := by
  have hs : support0116 = fromList transition0883Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0883Chunk0]
  have hn : (transition0883Raw0 : Multiset ℕ) = 1 • (supportNumbers1080 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1080] using hm

private def transition0884Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 544, 545, 546, 547, 928, 929, 930, 931]
private def transition0884Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 288, 289, 290, 291, 416, 417, 418, 419]
private theorem transition0884Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0884Input0) = fromList transition0884Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0884 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1080 = 1 • support1081 := by
  have hs : support1080 = fromList transition0884Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0884Chunk0]
  have hn : (transition0884Raw0 : Multiset ℕ) = 1 • (supportNumbers1081 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1081] using hm

private def transition0885Input0 : List ℕ := [0, 1, 2, 3, 384, 385, 386, 387, 544, 545, 546, 547, 928, 929, 930, 931]
private def transition0885Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition0885Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0885Input0) = fromList transition0885Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0885 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1080 = 1 • support1082 := by
  have hs : support1080 = fromList transition0885Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0885Chunk0]
  have hn : (transition0885Raw0 : Multiset ℕ) = 1 • (supportNumbers1082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1082] using hm

private def transition0886Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0886Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0886Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0886Input0) = fromList transition0886Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0886 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0117 = 1 • support0030 := by
  have hs : support0117 = fromList transition0886Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0886Chunk0]
  have hn : (transition0886Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0887Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0887Raw0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543]
private theorem transition0887Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0887Input0) = fromList transition0887Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0887 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0117 = 1 • support0191 := by
  have hs : support0117 = fromList transition0887Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0887Chunk0]
  have hn : (transition0887Raw0 : Multiset ℕ) = 1 • (supportNumbers0191 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0191] using hm

private def transition0888Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0888Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0888Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0888Input0) = fromList transition0888Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0888 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0117 = 1 • support0030 := by
  have hs : support0117 = fromList transition0888Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0888Chunk0]
  have hn : (transition0888Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0889Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0889Raw0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703]
private theorem transition0889Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0889Input0) = fromList transition0889Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0889 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0117 = 1 • support1084 := by
  have hs : support0117 = fromList transition0889Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0889Chunk0]
  have hn : (transition0889Raw0 : Multiset ℕ) = 1 • (supportNumbers1084 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1084] using hm

private def transition0890Input0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703]
private def transition0890Raw0 : List ℕ := [0, 1, 2, 3, 444, 445, 446, 447]
private theorem transition0890Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0890Input0) = fromList transition0890Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0890 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1084 = 1 • support1085 := by
  have hs : support1084 = fromList transition0890Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0890Chunk0]
  have hn : (transition0890Raw0 : Multiset ℕ) = 1 • (supportNumbers1085 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1085] using hm

private def transition0891Input0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703]
private def transition0891Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0891Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0891Input0) = fromList transition0891Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0891 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1084 = 1 • support1086 := by
  have hs : support1084 = fromList transition0891Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0891Chunk0]
  have hn : (transition0891Raw0 : Multiset ℕ) = 1 • (supportNumbers1086 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1086] using hm

private def transition0892Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0892Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0892Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0892Input0) = fromList transition0892Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0892 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0117 = 1 • support0117 := by
  have hs : support0117 = fromList transition0892Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0892Chunk0]
  have hn : (transition0892Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0893Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0893Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543]
private theorem transition0893Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0893Input0) = fromList transition0893Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0893 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0117 = 1 • support0192 := by
  have hs : support0117 = fromList transition0893Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0893Chunk0]
  have hn : (transition0893Raw0 : Multiset ℕ) = 1 • (supportNumbers0192 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0192] using hm

private def transition0894Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0894Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0894Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0894Input0) = fromList transition0894Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0894 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0117 = 1 • support0117 := by
  have hs : support0117 = fromList transition0894Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0894Chunk0]
  have hn : (transition0894Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0895Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private def transition0895Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703]
private theorem transition0895Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0895Input0) = fromList transition0895Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0895 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0117 = 1 • support1088 := by
  have hs : support0117 = fromList transition0895Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0895Chunk0]
  have hn : (transition0895Raw0 : Multiset ℕ) = 1 • (supportNumbers1088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1088] using hm

private def transition0896Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 544, 545, 546, 547, 700, 701, 702, 703]
private def transition0896Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 288, 289, 290, 291, 444, 445, 446, 447]
private theorem transition0896Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0896Input0) = fromList transition0896Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0896 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1088 = 1 • support0687 := by
  have hs : support1088 = fromList transition0896Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0896Chunk0]
  have hn : (transition0896Raw0 : Multiset ℕ) = 1 • (supportNumbers0687 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0687] using hm

private def transition0897Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 544, 545, 546, 547, 700, 701, 702, 703]
private def transition0897Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0897Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0897Input0) = fromList transition0897Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0897 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1088 = 1 • support0689 := by
  have hs : support1088 = fromList transition0897Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0897Chunk0]
  have hn : (transition0897Raw0 : Multiset ℕ) = 1 • (supportNumbers0689 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0689] using hm

private def transition0898Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0898Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition0898Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0898Input0) = fromList transition0898Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0898 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0118 = 1 • support0012 := by
  have hs : support0118 = fromList transition0898Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0898Chunk0]
  have hn : (transition0898Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition0899Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0899Raw0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543, 28, 29, 30, 31, 512, 513, 514, 515]
private theorem transition0899Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0899Input0) = fromList transition0899Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0899 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0118 = 1 • support0193 := by
  have hs : support0118 = fromList transition0899Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0899Chunk0]
  have hn : (transition0899Raw0 : Multiset ℕ) = 1 • (supportNumbers0193 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0193] using hm

private def transition0900Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0900Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition0900Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0900Input0) = fromList transition0900Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0900 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0118 = 1 • support0012 := by
  have hs : support0118 = fromList transition0900Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0900Chunk0]
  have hn : (transition0900Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition0901Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387]
private def transition0901Raw0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703, 28, 29, 30, 31, 672, 673, 674, 675]
private theorem transition0901Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0901Input0) = fromList transition0901Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0901 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0118 = 1 • support1089 := by
  have hs : support0118 = fromList transition0901Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0901Chunk0]
  have hn : (transition0901Raw0 : Multiset ℕ) = 1 • (supportNumbers1089 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1089] using hm

private def transition0902Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition0902Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition0902Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0902Input0) = fromList transition0902Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0902 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1089 = 1 • support1090 := by
  have hs : support1089 = fromList transition0902Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0902Chunk0]
  have hn : (transition0902Raw0 : Multiset ℕ) = 1 • (supportNumbers1090 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1090] using hm

private def transition0903Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 672, 673, 674, 675, 700, 701, 702, 703]
private def transition0903Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0903Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0903Input0) = fromList transition0903Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0903 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1089 = 1 • support1091 := by
  have hs : support1089 = fromList transition0903Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0903Chunk0]
  have hn : (transition0903Raw0 : Multiset ℕ) = 1 • (supportNumbers1091 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1091] using hm

private def transition0904Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 540, 541, 542, 543, 640, 641, 642, 643, 768, 769, 770, 771, 924, 925, 926, 927]
private def transition0904Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 28, 29, 30, 31, 128, 129, 130, 131, 284, 285, 286, 287, 384, 385, 386, 387, 256, 257, 258, 259, 412, 413, 414, 415]
private theorem transition0904Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0904Input0) = fromList transition0904Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0904 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0119 = 1 • support0194 := by
  have hs : support0119 = fromList transition0904Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0904Chunk0]
  have hn : (transition0904Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition0905Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 540, 541, 542, 543, 640, 641, 642, 643, 768, 769, 770, 771, 924, 925, 926, 927]
private def transition0905Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 256, 896, 257, 897, 258, 898, 259, 899, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0905Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0905Input0) = fromList transition0905Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0905 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0119 = 1 • support0195 := by
  have hs : support0119 = fromList transition0905Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0905Chunk0]
  have hn : (transition0905Raw0 : Multiset ℕ) = 1 • (supportNumbers0195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0195] using hm

private def transition0906Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 540, 541, 542, 543, 640, 641, 642, 643, 768, 769, 770, 771, 924, 925, 926, 927]
private def transition0906Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 28, 29, 30, 31, 128, 129, 130, 131, 284, 285, 286, 287, 384, 385, 386, 387, 256, 257, 258, 259, 412, 413, 414, 415]
private theorem transition0906Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0906Input0) = fromList transition0906Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0906 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0119 = 1 • support0194 := by
  have hs : support0119 = fromList transition0906Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0906Chunk0]
  have hn : (transition0906Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition0907Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0907Raw0 : List ℕ := [0, 1, 28, 29, 128, 129, 156, 157, 2, 3, 30, 31, 130, 131, 158, 159]
private theorem transition0907Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0907Input0) = fromList transition0907Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0907 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0194 = 1 • support0279 := by
  have hs : support0194 = fromList transition0907Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0907Chunk0]
  have hn : (transition0907Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition0908Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0908Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 128, 129, 706, 707, 156, 157, 734, 735, 576, 577, 2, 3, 604, 605, 30, 31, 704, 705, 130, 131, 732, 733, 158, 159]
private theorem transition0908Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0908Input0) = fromList transition0908Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0908 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0194 = 1 • support1093 := by
  have hs : support0194 = fromList transition0908Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0908Chunk0]
  have hn : (transition0908Raw0 : Multiset ℕ) = 1 • (supportNumbers1093 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1093] using hm

private def transition0909Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 284, 285, 286, 287, 384, 385, 386, 387, 540, 541, 542, 543, 640, 641, 642, 643, 768, 769, 770, 771, 924, 925, 926, 927]
private def transition0909Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 256, 800, 257, 801, 258, 802, 259, 803, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0909Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0909Input0) = fromList transition0909Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0909 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0119 = 1 • support1095 := by
  have hs : support0119 = fromList transition0909Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0909Chunk0]
  have hn : (transition0909Raw0 : Multiset ℕ) = 1 • (supportNumbers1095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1095] using hm

private def transition0910Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 672, 673, 674, 675, 700, 701, 702, 703, 800, 801, 802, 803, 828, 829, 830, 831, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition0910Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 288, 289, 290, 291, 316, 317, 318, 319, 416, 417, 418, 419, 444, 445, 446, 447, 288, 289, 290, 291, 316, 317, 318, 319, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition0910Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0910Input0) = fromList transition0910Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0910 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1095 = 2 • support0861 := by
  have hs : support1095 = fromList transition0910Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0910Chunk0]
  have hn : (transition0910Raw0 : Multiset ℕ) = 2 • (supportNumbers0861 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0861] using hm

private def transition0911Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 672, 673, 674, 675, 700, 701, 702, 703, 800, 801, 802, 803, 828, 829, 830, 831, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition0911Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735, 0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0911Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0911Input0) = fromList transition0911Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0911 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1095 = 2 • support0863 := by
  have hs : support1095 = fromList transition0911Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0911Chunk0]
  have hn : (transition0911Raw0 : Multiset ℕ) = 2 • (supportNumbers0863 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0863] using hm

private def transition0912Input0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523]
private def transition0912Raw0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private theorem transition0912Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0912Input0) = fromList transition0912Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0912 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0120 = 1 • support0196 := by
  have hs : support0120 = fromList transition0912Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0912Chunk0]
  have hn : (transition0912Raw0 : Multiset ℕ) = 1 • (supportNumbers0196 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0196] using hm

private def transition0913Input0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523]
private def transition0913Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 264, 904, 265, 905, 266, 906, 267, 907]
private theorem transition0913Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0913Input0) = fromList transition0913Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0913 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0120 = 1 • support0197 := by
  have hs : support0120 = fromList transition0913Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0913Chunk0]
  have hn : (transition0913Raw0 : Multiset ℕ) = 1 • (supportNumbers0197 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0197] using hm

private def transition0914Input0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523]
private def transition0914Raw0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private theorem transition0914Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0914Input0) = fromList transition0914Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0914 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0120 = 1 • support0196 := by
  have hs : support0120 = fromList transition0914Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0914Chunk0]
  have hn : (transition0914Raw0 : Multiset ℕ) = 1 • (supportNumbers0196 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0196] using hm

private def transition0915Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition0915Raw0 : List ℕ := [0, 1, 10, 11]
private theorem transition0915Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0915Input0) = fromList transition0915Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0915 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0196 = 1 • support0885 := by
  have hs : support0196 = fromList transition0915Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0915Chunk0]
  have hn : (transition0915Raw0 : Multiset ℕ) = 1 • (supportNumbers0885 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0885] using hm

private def transition0916Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267]
private def transition0916Raw0 : List ℕ := [0, 1, 578, 579, 584, 585, 10, 11]
private theorem transition0916Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0916Input0) = fromList transition0916Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0916 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0196 = 1 • support1096 := by
  have hs : support0196 = fromList transition0916Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0916Chunk0]
  have hn : (transition0916Raw0 : Multiset ℕ) = 1 • (supportNumbers1096 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1096] using hm

private def transition0917Input0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523]
private def transition0917Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 264, 808, 265, 809, 266, 810, 267, 811]
private theorem transition0917Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0917Input0) = fromList transition0917Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0917 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0120 = 1 • support1098 := by
  have hs : support0120 = fromList transition0917Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0917Chunk0]
  have hn : (transition0917Raw0 : Multiset ℕ) = 1 • (supportNumbers1098 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1098] using hm

private def transition0918Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 544, 545, 546, 547, 808, 809, 810, 811]
private def transition0918Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 288, 289, 290, 291, 296, 297, 298, 299]
private theorem transition0918Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0918Input0) = fromList transition0918Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0918 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1098 = 1 • support1099 := by
  have hs : support1098 = fromList transition0918Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0918Chunk0]
  have hn : (transition0918Raw0 : Multiset ℕ) = 1 • (supportNumbers1099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1099] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
