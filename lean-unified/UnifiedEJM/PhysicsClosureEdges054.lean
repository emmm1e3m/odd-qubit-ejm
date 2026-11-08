import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0919Input0 : List ℕ := [0, 1, 2, 3, 264, 265, 266, 267, 544, 545, 546, 547, 808, 809, 810, 811]
private def transition0919Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875]
private theorem transition0919Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0919Input0) = fromList transition0919Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0919 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1098 = 1 • support1100 := by
  have hs : support1098 = fromList transition0919Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0919Chunk0]
  have hn : (transition0919Raw0 : Multiset ℕ) = 1 • (supportNumbers1100 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1100] using hm

private def transition0920Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0920Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0920Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0920Input0) = fromList transition0920Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0920 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0121 = 1 • support0117 := by
  have hs : support0121 = fromList transition0920Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0920Chunk0]
  have hn : (transition0920Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0921Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0921Raw0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523, 660, 661, 662, 663, 156, 157, 158, 159]
private theorem transition0921Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0921Input0) = fromList transition0921Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0921 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0121 = 1 • support0198 := by
  have hs : support0121 = fromList transition0921Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0921Chunk0]
  have hn : (transition0921Raw0 : Multiset ℕ) = 1 • (supportNumbers0198 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0198] using hm

private def transition0922Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0922Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition0922Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0922Input0) = fromList transition0922Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0922 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0121 = 1 • support0117 := by
  have hs : support0121 = fromList transition0922Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0922Chunk0]
  have hn : (transition0922Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition0923Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415]
private def transition0923Raw0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683, 564, 565, 566, 567, 156, 157, 158, 159]
private theorem transition0923Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0923Input0) = fromList transition0923Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0923 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0121 = 1 • support1102 := by
  have hs : support0121 = fromList transition0923Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0923Chunk0]
  have hn : (transition0923Raw0 : Multiset ℕ) = 1 • (supportNumbers1102 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1102] using hm

private def transition0924Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 564, 565, 566, 567, 680, 681, 682, 683]
private def transition0924Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 308, 309, 310, 311, 424, 425, 426, 427]
private theorem transition0924Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0924Input0) = fromList transition0924Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0924 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1102 = 1 • support1103 := by
  have hs : support1102 = fromList transition0924Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0924Chunk0]
  have hn : (transition0924Raw0 : Multiset ℕ) = 1 • (supportNumbers1103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1103] using hm

private def transition0925Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 564, 565, 566, 567, 680, 681, 682, 683]
private def transition0925Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0925Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0925Input0) = fromList transition0925Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0925 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1102 = 1 • support1104 := by
  have hs : support1102 = fromList transition0925Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0925Chunk0]
  have hn : (transition0925Raw0 : Multiset ℕ) = 1 • (supportNumbers1104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1104] using hm

private def transition0926Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 520, 521, 522, 523, 640, 641, 642, 643, 796, 797, 798, 799, 916, 917, 918, 919]
private def transition0926Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 20, 21, 22, 23, 156, 157, 158, 159, 264, 265, 266, 267, 384, 385, 386, 387, 284, 285, 286, 287, 404, 405, 406, 407]
private theorem transition0926Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0926Input0) = fromList transition0926Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0926 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0122 = 1 • support0128 := by
  have hs : support0122 = fromList transition0926Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0926Chunk0]
  have hn : (transition0926Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0927Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 520, 521, 522, 523, 640, 641, 642, 643, 796, 797, 798, 799, 916, 917, 918, 919]
private def transition0927Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 20, 660, 21, 661, 22, 662, 23, 663, 156, 540, 157, 541, 158, 542, 159, 543, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 284, 924, 285, 925, 286, 926, 287, 927, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition0927Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0927Input0) = fromList transition0927Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0927 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0122 = 1 • support0129 := by
  have hs : support0122 = fromList transition0927Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0927Chunk0]
  have hn : (transition0927Raw0 : Multiset ℕ) = 1 • (supportNumbers0129 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0129] using hm

private def transition0928Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 520, 521, 522, 523, 640, 641, 642, 643, 796, 797, 798, 799, 916, 917, 918, 919]
private def transition0928Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 20, 21, 22, 23, 156, 157, 158, 159, 264, 265, 266, 267, 384, 385, 386, 387, 284, 285, 286, 287, 404, 405, 406, 407]
private theorem transition0928Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0928Input0) = fromList transition0928Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0928 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0122 = 1 • support0128 := by
  have hs : support0122 = fromList transition0928Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0928Chunk0]
  have hn : (transition0928Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0929Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 276, 277, 278, 279, 412, 413, 414, 415, 520, 521, 522, 523, 640, 641, 642, 643, 796, 797, 798, 799, 916, 917, 918, 919]
private def transition0929Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 20, 564, 21, 565, 22, 566, 23, 567, 156, 700, 157, 701, 158, 702, 159, 703, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 284, 828, 285, 829, 286, 830, 287, 831, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition0929Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0929Input0) = fromList transition0929Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0929 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0122 = 1 • support0896 := by
  have hs : support0122 = fromList transition0929Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0929Chunk0]
  have hn : (transition0929Raw0 : Multiset ℕ) = 1 • (supportNumbers0896 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0896] using hm

private def transition0930Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0930Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition0930Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0930Input0) = fromList transition0930Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0930 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0123 = 1 • support0199 := by
  have hs : support0123 = fromList transition0930Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0930Chunk0]
  have hn : (transition0930Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition0931Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0931Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 148, 149, 150, 151, 540, 541, 542, 543]
private theorem transition0931Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0931Input0) = fromList transition0931Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0931 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0123 = 1 • support0200 := by
  have hs : support0123 = fromList transition0931Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0931Chunk0]
  have hn : (transition0931Raw0 : Multiset ℕ) = 1 • (supportNumbers0200 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0200] using hm

private def transition0932Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0932Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition0932Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0932Input0) = fromList transition0932Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0932 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0123 = 1 • support0199 := by
  have hs : support0123 = fromList transition0932Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0932Chunk0]
  have hn : (transition0932Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition0933Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition0933Raw0 : List ℕ := [0, 1, 148, 149]
private theorem transition0933Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0933Input0) = fromList transition0933Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0933 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0199 = 1 • support1106 := by
  have hs : support0199 = fromList transition0933Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0933Chunk0]
  have hn : (transition0933Raw0 : Multiset ℕ) = 1 • (supportNumbers1106 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1106] using hm

private def transition0934Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition0934Raw0 : List ℕ := [0, 1, 578, 579, 148, 149, 726, 727]
private theorem transition0934Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0934Input0) = fromList transition0934Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0934 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0199 = 1 • support1107 := by
  have hs : support0199 = fromList transition0934Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0934Chunk0]
  have hn : (transition0934Raw0 : Multiset ℕ) = 1 • (supportNumbers1107 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1107] using hm

private def transition0935Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition0935Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 148, 149, 150, 151, 700, 701, 702, 703]
private theorem transition0935Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0935Input0) = fromList transition0935Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0935 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0123 = 1 • support1109 := by
  have hs : support0123 = fromList transition0935Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0935Chunk0]
  have hn : (transition0935Raw0 : Multiset ℕ) = 1 • (supportNumbers1109 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1109] using hm

private def transition0936Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 552, 553, 554, 555, 700, 701, 702, 703]
private def transition0936Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 296, 297, 298, 299, 444, 445, 446, 447]
private theorem transition0936Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0936Input0) = fromList transition0936Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0936 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1109 = 1 • support1110 := by
  have hs : support1109 = fromList transition0936Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0936Chunk0]
  have hn : (transition0936Raw0 : Multiset ℕ) = 1 • (supportNumbers1110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1110] using hm

private def transition0937Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 552, 553, 554, 555, 700, 701, 702, 703]
private def transition0937Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 296, 872, 297, 873, 298, 874, 299, 875, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0937Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0937Input0) = fromList transition0937Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0937 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1109 = 1 • support1111 := by
  have hs : support1109 = fromList transition0937Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0937Chunk0]
  have hn : (transition0937Raw0 : Multiset ℕ) = 1 • (supportNumbers1111 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1111] using hm

private def transition0938Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0938Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0938Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0938Input0) = fromList transition0938Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0938 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0124 = 1 • support0201 := by
  have hs : support0124 = fromList transition0938Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0938Chunk0]
  have hn : (transition0938Raw0 : Multiset ℕ) = 1 • (supportNumbers0201 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0201] using hm

private def transition0939Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0939Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0939Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0939Input0) = fromList transition0939Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0939 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0124 = 1 • support0202 := by
  have hs : support0124 = fromList transition0939Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0939Chunk0]
  have hn : (transition0939Raw0 : Multiset ℕ) = 1 • (supportNumbers0202 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0202] using hm

private def transition0940Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0940Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0940Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0940Input0) = fromList transition0940Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0940 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0124 = 1 • support0201 := by
  have hs : support0124 = fromList transition0940Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0940Chunk0]
  have hn : (transition0940Raw0 : Multiset ℕ) = 1 • (supportNumbers0201 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0201] using hm

private def transition0941Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0941Raw0 : List ℕ := [0, 1, 8, 9, 148, 149, 156, 157, 2, 3, 10, 11, 150, 151, 158, 159]
private theorem transition0941Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0941Input0) = fromList transition0941Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0941 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0201 = 1 • support0123 := by
  have hs : support0201 = fromList transition0941Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0941Chunk0]
  have hn : (transition0941Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition0942Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0942Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 148, 149, 726, 727, 156, 157, 734, 735, 576, 577, 2, 3, 584, 585, 10, 11, 724, 725, 150, 151, 732, 733, 158, 159]
private theorem transition0942Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0942Input0) = fromList transition0942Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0942 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0201 = 1 • support1113 := by
  have hs : support0201 = fromList transition0942Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0942Chunk0]
  have hn : (transition0942Raw0 : Multiset ℕ) = 1 • (supportNumbers1113 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1113] using hm

private def transition0943Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 512, 513, 514, 515, 520, 521, 522, 523, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition0943Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0943Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0943Input0) = fromList transition0943Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0943 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0124 = 1 • support1115 := by
  have hs : support0124 = fromList transition0943Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0943Chunk0]
  have hn : (transition0943Raw0 : Multiset ℕ) = 1 • (supportNumbers1115 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1115] using hm

private def transition0944Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703, 800, 801, 802, 803, 808, 809, 810, 811, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0944Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition0944Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0944Input0) = fromList transition0944Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0944 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1115 = 2 • support1116 := by
  have hs : support1115 = fromList transition0944Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0944Chunk0]
  have hn : (transition0944Raw0 : Multiset ℕ) = 2 • (supportNumbers1116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1116] using hm

private def transition0945Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703, 800, 801, 802, 803, 808, 809, 810, 811, 948, 949, 950, 951, 956, 957, 958, 959]
private def transition0945Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0945Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0945Input0) = fromList transition0945Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0945 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1115 = 2 • support1118 := by
  have hs : support1115 = fromList transition0945Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0945Chunk0]
  have hn : (transition0945Raw0 : Multiset ℕ) = 2 • (supportNumbers1118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1118] using hm

private def transition0946Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0946Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0946Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0946Input0) = fromList transition0946Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0946 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0946Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0946Chunk0]
  have hn : (transition0946Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0947Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0947Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663]
private theorem transition0947Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0947Input0) = fromList transition0947Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0947 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0069 = 1 • support0203 := by
  have hs : support0069 = fromList transition0947Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0947Chunk0]
  have hn : (transition0947Raw0 : Multiset ℕ) = 1 • (supportNumbers0203 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0203] using hm

private def transition0948Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0948Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0948Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0948Input0) = fromList transition0948Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0948 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0948Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0948Chunk0]
  have hn : (transition0948Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0949Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0949Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567]
private theorem transition0949Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0949Input0) = fromList transition0949Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0949 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0069 = 1 • support1120 := by
  have hs : support0069 = fromList transition0949Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0949Chunk0]
  have hn : (transition0949Raw0 : Multiset ℕ) = 1 • (supportNumbers1120 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1120] using hm

private def transition0950Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 544, 545, 546, 547, 564, 565, 566, 567]
private def transition0950Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 288, 289, 290, 291, 308, 309, 310, 311]
private theorem transition0950Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0950Input0) = fromList transition0950Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0950 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1120 = 1 • support1121 := by
  have hs : support1120 = fromList transition0950Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0950Chunk0]
  have hn : (transition0950Raw0 : Multiset ℕ) = 1 • (supportNumbers1121 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1121] using hm

private def transition0951Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 544, 545, 546, 547, 564, 565, 566, 567]
private def transition0951Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887]
private theorem transition0951Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0951Input0) = fromList transition0951Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0951 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1120 = 1 • support1122 := by
  have hs : support1120 = fromList transition0951Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0951Chunk0]
  have hn : (transition0951Raw0 : Multiset ℕ) = 1 • (supportNumbers1122 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1122] using hm

private def transition0952Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0952Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0952Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0952Input0) = fromList transition0952Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0952 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0125 = 1 • support0204 := by
  have hs : support0125 = fromList transition0952Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0952Chunk0]
  have hn : (transition0952Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0953Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0953Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0953Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0953Input0) = fromList transition0953Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0953 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0125 = 1 • support0204 := by
  have hs : support0125 = fromList transition0953Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0953Chunk0]
  have hn : (transition0953Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0954Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0954Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0954Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0954Input0) = fromList transition0954Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0954 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0125 = 1 • support0204 := by
  have hs : support0125 = fromList transition0954Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0954Chunk0]
  have hn : (transition0954Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0955Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition0955Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29]
private theorem transition0955Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0955Input0) = fromList transition0955Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0955 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0204 = 1 • support1124 := by
  have hs : support0204 = fromList transition0955Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0955Chunk0]
  have hn : (transition0955Raw0 : Multiset ℕ) = 1 • (supportNumbers1124 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1124] using hm

private def transition0956Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition0956Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 20, 21, 598, 599, 28, 29, 606, 607]
private theorem transition0956Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0956Input0) = fromList transition0956Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0956 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0204 = 1 • support1125 := by
  have hs : support0204 = fromList transition0956Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0956Chunk0]
  have hn : (transition0956Raw0 : Multiset ℕ) = 1 • (supportNumbers1125 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1125] using hm

private def transition0957Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0957Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0957Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0957Input0) = fromList transition0957Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0957 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0125 = 1 • support0204 := by
  have hs : support0125 = fromList transition0957Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0957Chunk0]
  have hn : (transition0957Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0958Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition0958Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private theorem transition0958Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0958Input0) = fromList transition0958Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0958 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0204 = 1 • support0204 := by
  have hs : support0204 = fromList transition0958Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0958Chunk0]
  have hn : (transition0958Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0959Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition0959Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607]
private theorem transition0959Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0959Input0) = fromList transition0959Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0959 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0204 = 1 • support1127 := by
  have hs : support0204 = fromList transition0959Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0959Chunk0]
  have hn : (transition0959Raw0 : Multiset ℕ) = 1 • (supportNumbers1127 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1127] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
