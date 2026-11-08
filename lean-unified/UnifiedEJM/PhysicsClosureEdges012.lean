import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0222Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 544, 546, 681, 683, 801, 803, 936, 938]
private def transition0222Raw0 : List ℕ := [0, 2, 137, 139, 1, 3, 136, 138, 288, 290, 425, 427, 289, 291, 424, 426]
private theorem transition0222Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0222Input0) = fromList transition0222Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0222 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0667 = 1 • support0668 := by
  have hs : support0667 = fromList transition0222Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0222Chunk0]
  have hn : (transition0222Raw0 : Multiset ℕ) = 1 • (supportNumbers0668 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0668] using hm

private def transition0223Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 544, 546, 681, 683, 801, 803, 936, 938]
private def transition0223Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 1, 577, 3, 579, 136, 712, 138, 714, 288, 864, 290, 866, 425, 1001, 427, 1003, 289, 865, 291, 867, 424, 1000, 426, 1002]
private theorem transition0223Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0223Input0) = fromList transition0223Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0223 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0667 = 1 • support0669 := by
  have hs : support0667 = fromList transition0223Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0223Chunk0]
  have hn : (transition0223Raw0 : Multiset ℕ) = 1 • (supportNumbers0669 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0669] using hm

private def transition0224Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0224Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition0224Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0224Input0) = fromList transition0224Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0224 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0028 = 1 • support0059 := by
  have hs : support0028 = fromList transition0224Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0224Chunk0]
  have hn : (transition0224Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition0225Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0225Raw0 : List ℕ := [0, 2, 648, 650, 129, 131, 521, 523, 641, 643, 9, 11, 512, 514, 136, 138]
private theorem transition0225Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0225Input0) = fromList transition0225Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0225 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0028 = 1 • support0060 := by
  have hs : support0028 = fromList transition0225Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0225Chunk0]
  have hn : (transition0225Raw0 : Multiset ℕ) = 1 • (supportNumbers0060 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0060] using hm

private def transition0226Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0226Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition0226Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0226Input0) = fromList transition0226Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0226 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0028 = 1 • support0059 := by
  have hs : support0028 = fromList transition0226Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0226Chunk0]
  have hn : (transition0226Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition0227Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0227Raw0 : List ℕ := [0, 9, 129, 136]
private theorem transition0227Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0227Input0) = fromList transition0227Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0227 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0059 = 1 • support0671 := by
  have hs : support0059 = fromList transition0227Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0227Chunk0]
  have hn : (transition0227Raw0 : Multiset ℕ) = 1 • (supportNumbers0671 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0671] using hm

private def transition0228Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0228Raw0 : List ℕ := [0, 578, 9, 587, 129, 707, 136, 714]
private theorem transition0228Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0228Input0) = fromList transition0228Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0228 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0059 = 1 • support0672 := by
  have hs : support0059 = fromList transition0228Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0228Chunk0]
  have hn : (transition0228Raw0 : Multiset ℕ) = 1 • (supportNumbers0672 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0672] using hm

private def transition0229Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private def transition0229Raw0 : List ℕ := [0, 2, 552, 554, 129, 131, 681, 683, 545, 547, 9, 11, 672, 674, 136, 138]
private theorem transition0229Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0229Input0) = fromList transition0229Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0229 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0028 = 1 • support0674 := by
  have hs : support0028 = fromList transition0229Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0229Chunk0]
  have hn : (transition0229Raw0 : Multiset ℕ) = 1 • (supportNumbers0674 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0674] using hm

private def transition0230Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 545, 547, 552, 554, 672, 674, 681, 683]
private def transition0230Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 289, 291, 296, 298, 416, 418, 425, 427]
private theorem transition0230Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0230Input0) = fromList transition0230Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0230 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0674 = 1 • support0675 := by
  have hs : support0674 = fromList transition0230Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0230Chunk0]
  have hn : (transition0230Raw0 : Multiset ℕ) = 1 • (supportNumbers0675 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0675] using hm

private def transition0231Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 545, 547, 552, 554, 672, 674, 681, 683]
private def transition0231Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714, 289, 865, 291, 867, 296, 872, 298, 874, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition0231Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0231Input0) = fromList transition0231Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0231 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0674 = 1 • support0676 := by
  have hs : support0674 = fromList transition0231Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0231Chunk0]
  have hn : (transition0231Raw0 : Multiset ℕ) = 1 • (supportNumbers0676 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0676] using hm

private def transition0232Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 513, 515, 521, 523, 640, 642, 648, 650, 768, 770, 776, 778, 897, 899, 905, 907]
private def transition0232Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 1, 3, 9, 11, 128, 130, 136, 138, 257, 259, 265, 267, 384, 386, 392, 394, 256, 258, 264, 266, 385, 387, 393, 395]
private theorem transition0232Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0232Input0) = fromList transition0232Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0232 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0029 = 1 • support0061 := by
  have hs : support0029 = fromList transition0232Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0232Chunk0]
  have hn : (transition0232Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0233Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 513, 515, 521, 523, 640, 642, 648, 650, 768, 770, 776, 778, 897, 899, 905, 907]
private def transition0233Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 1, 641, 3, 643, 9, 649, 11, 651, 128, 512, 130, 514, 136, 520, 138, 522, 257, 897, 259, 899, 265, 905, 267, 907, 384, 768, 386, 770, 392, 776, 394, 778, 256, 896, 258, 898, 264, 904, 266, 906, 385, 769, 387, 771, 393, 777, 395, 779]
private theorem transition0233Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0233Input0) = fromList transition0233Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0233 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0029 = 1 • support0062 := by
  have hs : support0029 = fromList transition0233Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0233Chunk0]
  have hn : (transition0233Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition0234Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 513, 515, 521, 523, 640, 642, 648, 650, 768, 770, 776, 778, 897, 899, 905, 907]
private def transition0234Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 1, 3, 9, 11, 128, 130, 136, 138, 257, 259, 265, 267, 384, 386, 392, 394, 256, 258, 264, 266, 385, 387, 393, 395]
private theorem transition0234Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0234Input0) = fromList transition0234Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0234 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0029 = 1 • support0061 := by
  have hs : support0029 = fromList transition0234Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0234Chunk0]
  have hn : (transition0234Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition0235Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0235Raw0 : List ℕ := [0, 1, 8, 9, 128, 129, 136, 137, 2, 3, 10, 11, 130, 131, 138, 139]
private theorem transition0235Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0235Input0) = fromList transition0235Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0235 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0061 = 1 • support0114 := by
  have hs : support0061 = fromList transition0235Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0235Chunk0]
  have hn : (transition0235Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition0236Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0236Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 128, 129, 706, 707, 136, 137, 714, 715, 576, 577, 2, 3, 584, 585, 10, 11, 704, 705, 130, 131, 712, 713, 138, 139]
private theorem transition0236Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0236Input0) = fromList transition0236Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0236 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0061 = 1 • support0678 := by
  have hs : support0061 = fromList transition0236Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0236Chunk0]
  have hn : (transition0236Raw0 : Multiset ℕ) = 1 • (supportNumbers0678 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0678] using hm

private def transition0237Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 513, 515, 521, 523, 640, 642, 648, 650, 768, 770, 776, 778, 897, 899, 905, 907]
private def transition0237Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 1, 545, 3, 547, 9, 553, 11, 555, 128, 672, 130, 674, 136, 680, 138, 682, 257, 801, 259, 803, 265, 809, 267, 811, 384, 928, 386, 930, 392, 936, 394, 938, 256, 800, 258, 802, 264, 808, 266, 810, 385, 929, 387, 931, 393, 937, 395, 939]
private theorem transition0237Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0237Input0) = fromList transition0237Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0237 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0029 = 1 • support0680 := by
  have hs : support0029 = fromList transition0237Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0237Chunk0]
  have hn : (transition0237Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition0238Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 672, 673, 674, 675, 680, 681, 682, 683, 800, 801, 802, 803, 808, 809, 810, 811, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition0238Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 288, 289, 290, 291, 296, 297, 298, 299, 416, 417, 418, 419, 424, 425, 426, 427, 288, 289, 290, 291, 296, 297, 298, 299, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition0238Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0238Input0) = fromList transition0238Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0238 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0680 = 2 • support0564 := by
  have hs : support0680 = fromList transition0238Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0238Chunk0]
  have hn : (transition0238Raw0 : Multiset ℕ) = 2 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition0239Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 672, 673, 674, 675, 680, 681, 682, 683, 800, 801, 802, 803, 808, 809, 810, 811, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition0239Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0239Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0239Input0) = fromList transition0239Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0239 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0680 = 2 • support0565 := by
  have hs : support0680 = fromList transition0239Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0239Chunk0]
  have hn : (transition0239Raw0 : Multiset ℕ) = 2 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition0240Input0 : List ℕ := [0, 1, 2, 3]
private def transition0240Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0240Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0240Input0) = fromList transition0240Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0240 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0240Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0240Chunk0]
  have hn : (transition0240Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0241Input0 : List ℕ := [0, 1, 2, 3]
private def transition0241Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0241Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0241Input0) = fromList transition0241Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0241 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0241Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0241Chunk0]
  have hn : (transition0241Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0242Input0 : List ℕ := [0, 1, 2, 3]
private def transition0242Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0242Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0242Input0) = fromList transition0242Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0242 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0242Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0242Chunk0]
  have hn : (transition0242Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0243Input0 : List ℕ := [0, 1, 2, 3]
private def transition0243Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0243Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0243Input0) = fromList transition0243Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0243 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0243Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0243Chunk0]
  have hn : (transition0243Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0244Input0 : List ℕ := [0, 1, 2, 3]
private def transition0244Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition0244Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0244Input0) = fromList transition0244Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0244 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0030 = 1 • support0030 := by
  have hs : support0030 = fromList transition0244Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0244Chunk0]
  have hn : (transition0244Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition0245Input0 : List ℕ := [0, 1, 2, 3]
private def transition0245Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579]
private theorem transition0245Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0245Input0) = fromList transition0245Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0245 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0030 = 1 • support0681 := by
  have hs : support0030 = fromList transition0245Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0245Chunk0]
  have hn : (transition0245Raw0 : Multiset ℕ) = 1 • (supportNumbers0681 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0681] using hm

private def transition0246Input0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671]
private def transition0246Raw0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private theorem transition0246Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0246Input0) = fromList transition0246Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0246 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0031 = 1 • support0063 := by
  have hs : support0031 = fromList transition0246Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0246Chunk0]
  have hn : (transition0246Raw0 : Multiset ℕ) = 1 • (supportNumbers0063 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0063] using hm

private def transition0247Input0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671]
private def transition0247Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0247Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0247Input0) = fromList transition0247Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0247 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0031 = 1 • support0064 := by
  have hs : support0031 = fromList transition0247Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0247Chunk0]
  have hn : (transition0247Raw0 : Multiset ℕ) = 1 • (supportNumbers0064 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0064] using hm

private def transition0248Input0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671]
private def transition0248Raw0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private theorem transition0248Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0248Input0) = fromList transition0248Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0248 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0031 = 1 • support0063 := by
  have hs : support0031 = fromList transition0248Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0248Chunk0]
  have hn : (transition0248Raw0 : Multiset ℕ) = 1 • (supportNumbers0063 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0063] using hm

private def transition0249Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0249Raw0 : List ℕ := [0, 1, 158, 159]
private theorem transition0249Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0249Input0) = fromList transition0249Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0249 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0063 = 1 • support0683 := by
  have hs : support0063 = fromList transition0249Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0249Chunk0]
  have hn : (transition0249Raw0 : Multiset ℕ) = 1 • (supportNumbers0683 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0683] using hm

private def transition0250Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415]
private def transition0250Raw0 : List ℕ := [0, 1, 578, 579, 732, 733, 158, 159]
private theorem transition0250Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0250Input0) = fromList transition0250Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0250 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0063 = 1 • support0684 := by
  have hs : support0063 = fromList transition0250Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0250Chunk0]
  have hn : (transition0250Raw0 : Multiset ℕ) = 1 • (supportNumbers0684 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0684] using hm

private def transition0251Input0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671]
private def transition0251Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0251Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0251Input0) = fromList transition0251Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0251 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0031 = 1 • support0686 := by
  have hs : support0031 = fromList transition0251Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0251Chunk0]
  have hn : (transition0251Raw0 : Multiset ℕ) = 1 • (supportNumbers0686 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0686] using hm

private def transition0252Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 544, 545, 546, 547, 956, 957, 958, 959]
private def transition0252Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 288, 289, 290, 291, 444, 445, 446, 447]
private theorem transition0252Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0252Input0) = fromList transition0252Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0252 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0686 = 1 • support0687 := by
  have hs : support0686 = fromList transition0252Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0252Chunk0]
  have hn : (transition0252Raw0 : Multiset ℕ) = 1 • (supportNumbers0687 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0687] using hm

private def transition0253Input0 : List ℕ := [0, 1, 2, 3, 412, 413, 414, 415, 544, 545, 546, 547, 956, 957, 958, 959]
private def transition0253Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0253Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0253Input0) = fromList transition0253Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0253 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0686 = 1 • support0689 := by
  have hs : support0686 = fromList transition0253Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0253Chunk0]
  have hn : (transition0253Raw0 : Multiset ℕ) = 1 • (supportNumbers0689 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0689] using hm

private def transition0254Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0254Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition0254Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0254Input0) = fromList transition0254Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0254 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0032 = 1 • support0065 := by
  have hs : support0032 = fromList transition0254Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0254Chunk0]
  have hn : (transition0254Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition0255Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0255Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 136, 137, 138, 139, 532, 533, 534, 535]
private theorem transition0255Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0255Input0) = fromList transition0255Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0255 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0032 = 1 • support0066 := by
  have hs : support0032 = fromList transition0255Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0255Chunk0]
  have hn : (transition0255Raw0 : Multiset ℕ) = 1 • (supportNumbers0066 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0066] using hm

private def transition0256Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0256Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition0256Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0256Input0) = fromList transition0256Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0256 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0032 = 1 • support0065 := by
  have hs : support0032 = fromList transition0256Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0256Chunk0]
  have hn : (transition0256Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition0257Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0257Raw0 : List ℕ := [0, 1, 136, 137]
private theorem transition0257Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0257Input0) = fromList transition0257Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0257 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0065 = 1 • support0584 := by
  have hs : support0065 = fromList transition0257Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0257Chunk0]
  have hn : (transition0257Raw0 : Multiset ℕ) = 1 • (supportNumbers0584 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0584] using hm

private def transition0258Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition0258Raw0 : List ℕ := [0, 1, 578, 579, 136, 137, 714, 715]
private theorem transition0258Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0258Input0) = fromList transition0258Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0258 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0065 = 1 • support0691 := by
  have hs : support0065 = fromList transition0258Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0258Chunk0]
  have hn : (transition0258Raw0 : Multiset ℕ) = 1 • (supportNumbers0691 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0691] using hm

private def transition0259Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition0259Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 136, 137, 138, 139, 692, 693, 694, 695]
private theorem transition0259Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0259Input0) = fromList transition0259Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0259 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0032 = 1 • support0693 := by
  have hs : support0032 = fromList transition0259Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0259Chunk0]
  have hn : (transition0259Raw0 : Multiset ℕ) = 1 • (supportNumbers0693 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0693] using hm

private def transition0260Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 572, 573, 574, 575, 692, 693, 694, 695]
private def transition0260Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 316, 317, 318, 319, 436, 437, 438, 439]
private theorem transition0260Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0260Input0) = fromList transition0260Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0260 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0693 = 1 • support0694 := by
  have hs : support0693 = fromList transition0260Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0260Chunk0]
  have hn : (transition0260Raw0 : Multiset ℕ) = 1 • (supportNumbers0694 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0694] using hm

private def transition0261Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 572, 573, 574, 575, 692, 693, 694, 695]
private def transition0261Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 316, 892, 317, 893, 318, 894, 319, 895, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition0261Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0261Input0) = fromList transition0261Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0261 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0693 = 1 • support0695 := by
  have hs : support0693 = fromList transition0261Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0261Chunk0]
  have hn : (transition0261Raw0 : Multiset ℕ) = 1 • (supportNumbers0695 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0695] using hm

private def transition0262Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791]
private def transition0262Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 384, 385, 386, 387, 412, 413, 414, 415, 264, 265, 266, 267, 276, 277, 278, 279]
private theorem transition0262Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0262Input0) = fromList transition0262Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0262 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0033 = 1 • support0067 := by
  have hs : support0033 = fromList transition0262Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0262Chunk0]
  have hn : (transition0262Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition0263Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791]
private def transition0263Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919]
private theorem transition0263Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0263Input0) = fromList transition0263Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0263 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0033 = 1 • support0068 := by
  have hs : support0033 = fromList transition0263Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0263Chunk0]
  have hn : (transition0263Raw0 : Multiset ℕ) = 1 • (supportNumbers0068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0068] using hm

private def transition0264Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791]
private def transition0264Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 384, 385, 386, 387, 412, 413, 414, 415, 264, 265, 266, 267, 276, 277, 278, 279]
private theorem transition0264Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0264Input0) = fromList transition0264Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0264 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0033 = 1 • support0067 := by
  have hs : support0033 = fromList transition0264Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0264Chunk0]
  have hn : (transition0264Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition0265Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0265Raw0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149, 10, 11, 22, 23, 130, 131, 158, 159]
private theorem transition0265Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0265Input0) = fromList transition0265Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0265 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0067 = 1 • support0697 := by
  have hs : support0067 = fromList transition0265Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0265Chunk0]
  have hn : (transition0265Raw0 : Multiset ℕ) = 1 • (supportNumbers0697 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0697] using hm

private def transition0266Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition0266Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 136, 137, 714, 715, 148, 149, 726, 727, 584, 585, 10, 11, 596, 597, 22, 23, 704, 705, 130, 131, 732, 733, 158, 159]
private theorem transition0266Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0266Input0) = fromList transition0266Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0266 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0067 = 1 • support0699 := by
  have hs : support0067 = fromList transition0266Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0266Chunk0]
  have hn : (transition0266Raw0 : Multiset ℕ) = 1 • (supportNumbers0699 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0699] using hm

private def transition0267Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 392, 393, 394, 395, 404, 405, 406, 407, 640, 641, 642, 643, 668, 669, 670, 671, 776, 777, 778, 779, 788, 789, 790, 791]
private def transition0267Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823]
private theorem transition0267Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0267Input0) = fromList transition0267Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0267 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0033 = 1 • support0701 := by
  have hs : support0033 = fromList transition0267Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0267Chunk0]
  have hn : (transition0267Raw0 : Multiset ℕ) = 1 • (supportNumbers0701 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0701] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
