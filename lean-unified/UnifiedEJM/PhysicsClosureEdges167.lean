import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2870Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 544, 545, 546, 547, 700, 701, 702, 703, 800, 801, 802, 803, 956, 957, 958, 959]
private def transition2870Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 0, 1, 2, 3, 156, 157, 158, 159, 288, 289, 290, 291, 444, 445, 446, 447, 288, 289, 290, 291, 444, 445, 446, 447]
private theorem transition2870Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2870Input0) = fromList transition2870Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2870 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1742 = 2 • support0687 := by
  have hs : support1742 = fromList transition2870Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2870Chunk0]
  have hn : (transition2870Raw0 : Multiset ℕ) = 2 • (supportNumbers0687 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0687] using hm

private def transition2871Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415, 544, 545, 546, 547, 700, 701, 702, 703, 800, 801, 802, 803, 956, 957, 958, 959]
private def transition2871Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2871Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2871Input0) = fromList transition2871Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2871 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1742 = 2 • support0689 := by
  have hs : support1742 = fromList transition2871Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2871Chunk0]
  have hn : (transition2871Raw0 : Multiset ℕ) = 2 • (supportNumbers0689 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0689] using hm

private def transition2872Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2872Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition2872Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2872Input0) = fromList transition2872Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2872 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0425 = 1 • support0279 := by
  have hs : support0425 = fromList transition2872Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2872Chunk0]
  have hn : (transition2872Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition2873Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2873Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition2873Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2873Input0) = fromList transition2873Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2873 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0425 = 1 • support0279 := by
  have hs : support0425 = fromList transition2873Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2873Chunk0]
  have hn : (transition2873Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition2874Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2874Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition2874Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2874Input0) = fromList transition2874Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2874 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0425 = 1 • support0279 := by
  have hs : support0425 = fromList transition2874Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2874Chunk0]
  have hn : (transition2874Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition2875Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2875Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159]
private theorem transition2875Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2875Input0) = fromList transition2875Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2875 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0425 = 1 • support0279 := by
  have hs : support0425 = fromList transition2875Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2875Chunk0]
  have hn : (transition2875Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition2876Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition2876Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private theorem transition2876Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2876Input0) = fromList transition2876Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2876 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0279 = 1 • support0279 := by
  have hs : support0279 = fromList transition2876Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2876Chunk0]
  have hn : (transition2876Raw0 : Multiset ℕ) = 1 • (supportNumbers0279 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0279] using hm

private def transition2877Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition2877Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition2877Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2877Input0) = fromList transition2877Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2877 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0279 = 1 • support1093 := by
  have hs : support0279 = fromList transition2877Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2877Chunk0]
  have hn : (transition2877Raw0 : Multiset ℕ) = 1 • (supportNumbers1093 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1093] using hm

private def transition2878Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 512, 513, 514, 515, 640, 641, 642, 643, 796, 797, 798, 799, 924, 925, 926, 927]
private def transition2878Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159, 256, 257, 258, 259, 384, 385, 386, 387, 284, 285, 286, 287, 412, 413, 414, 415]
private theorem transition2878Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2878Input0) = fromList transition2878Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2878 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0426 = 1 • support0194 := by
  have hs : support0426 = fromList transition2878Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2878Chunk0]
  have hn : (transition2878Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2879Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 512, 513, 514, 515, 640, 641, 642, 643, 796, 797, 798, 799, 924, 925, 926, 927]
private def transition2879Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 28, 668, 29, 669, 30, 670, 31, 671, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 384, 768, 385, 769, 386, 770, 387, 771, 284, 924, 285, 925, 286, 926, 287, 927, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2879Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2879Input0) = fromList transition2879Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2879 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0426 = 1 • support0195 := by
  have hs : support0426 = fromList transition2879Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2879Chunk0]
  have hn : (transition2879Raw0 : Multiset ℕ) = 1 • (supportNumbers0195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0195] using hm

private def transition2880Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 512, 513, 514, 515, 640, 641, 642, 643, 796, 797, 798, 799, 924, 925, 926, 927]
private def transition2880Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159, 256, 257, 258, 259, 384, 385, 386, 387, 284, 285, 286, 287, 412, 413, 414, 415]
private theorem transition2880Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2880Input0) = fromList transition2880Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2880 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0426 = 1 • support0194 := by
  have hs : support0426 = fromList transition2880Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2880Chunk0]
  have hn : (transition2880Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2881Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 512, 513, 514, 515, 640, 641, 642, 643, 796, 797, 798, 799, 924, 925, 926, 927]
private def transition2881Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 28, 572, 29, 573, 30, 574, 31, 575, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 384, 928, 385, 929, 386, 930, 387, 931, 284, 828, 285, 829, 286, 830, 287, 831, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2881Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2881Input0) = fromList transition2881Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2881 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0426 = 1 • support1095 := by
  have hs : support0426 = fromList transition2881Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2881Chunk0]
  have hn : (transition2881Raw0 : Multiset ℕ) = 1 • (supportNumbers1095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1095] using hm

private def transition2882Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2882Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2882Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2882Input0) = fromList transition2882Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2882 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0427 = 1 • support0065 := by
  have hs : support0427 = fromList transition2882Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2882Chunk0]
  have hn : (transition2882Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2883Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2883Raw0 : List ℕ := [0, 1, 2, 3, 520, 521, 522, 523, 640, 641, 642, 643, 136, 137, 138, 139]
private theorem transition2883Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2883Input0) = fromList transition2883Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2883 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0427 = 1 • support1743 := by
  have hs : support0427 = fromList transition2883Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2883Chunk0]
  have hn : (transition2883Raw0 : Multiset ℕ) = 1 • (supportNumbers1743 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1743] using hm

private def transition2884Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2884Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2884Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2884Input0) = fromList transition2884Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2884 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0427 = 1 • support0065 := by
  have hs : support0427 = fromList transition2884Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2884Chunk0]
  have hn : (transition2884Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2885Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2885Raw0 : List ℕ := [0, 1, 2, 3, 680, 681, 682, 683, 544, 545, 546, 547, 136, 137, 138, 139]
private theorem transition2885Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2885Input0) = fromList transition2885Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2885 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0427 = 1 • support1744 := by
  have hs : support0427 = fromList transition2885Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2885Chunk0]
  have hn : (transition2885Raw0 : Multiset ℕ) = 1 • (supportNumbers1744 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1744] using hm

private def transition2886Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 544, 545, 546, 547, 680, 681, 682, 683]
private def transition2886Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 288, 289, 290, 291, 424, 425, 426, 427]
private theorem transition2886Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2886Input0) = fromList transition2886Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2886 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1744 = 1 • support0668 := by
  have hs : support1744 = fromList transition2886Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2886Chunk0]
  have hn : (transition2886Raw0 : Multiset ℕ) = 1 • (supportNumbers0668 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0668] using hm

private def transition2887Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 544, 545, 546, 547, 680, 681, 682, 683]
private def transition2887Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition2887Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2887Input0) = fromList transition2887Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2887 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1744 = 1 • support0669 := by
  have hs : support1744 = fromList transition2887Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2887Chunk0]
  have hn : (transition2887Raw0 : Multiset ℕ) = 1 • (supportNumbers0669 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0669] using hm

private def transition2888Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 520, 521, 522, 523, 640, 641, 642, 643, 776, 777, 778, 779, 896, 897, 898, 899]
private def transition2888Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 264, 265, 266, 267, 384, 385, 386, 387]
private theorem transition2888Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2888Input0) = fromList transition2888Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2888 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0428 = 2 • support0108 := by
  have hs : support0428 = fromList transition2888Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2888Chunk0]
  have hn : (transition2888Raw0 : Multiset ℕ) = 2 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition2889Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 520, 521, 522, 523, 640, 641, 642, 643, 776, 777, 778, 779, 896, 897, 898, 899]
private def transition2889Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771, 264, 904, 265, 905, 266, 906, 267, 907, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition2889Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2889Input0) = fromList transition2889Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2889 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0428 = 2 • support0109 := by
  have hs : support0428 = fromList transition2889Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2889Chunk0]
  have hn : (transition2889Raw0 : Multiset ℕ) = 2 • (supportNumbers0109 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0109] using hm

private def transition2890Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 520, 521, 522, 523, 640, 641, 642, 643, 776, 777, 778, 779, 896, 897, 898, 899]
private def transition2890Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 264, 265, 266, 267, 384, 385, 386, 387]
private theorem transition2890Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2890Input0) = fromList transition2890Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2890 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0428 = 2 • support0108 := by
  have hs : support0428 = fromList transition2890Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2890Chunk0]
  have hn : (transition2890Raw0 : Multiset ℕ) = 2 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition2891Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 520, 521, 522, 523, 640, 641, 642, 643, 776, 777, 778, 779, 896, 897, 898, 899]
private def transition2891Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931, 264, 808, 265, 809, 266, 810, 267, 811, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition2891Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2891Input0) = fromList transition2891Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2891 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0428 = 2 • support0830 := by
  have hs : support0428 = fromList transition2891Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2891Chunk0]
  have hn : (transition2891Raw0 : Multiset ℕ) = 2 • (supportNumbers0830 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0830] using hm

private def transition2892Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2892Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2892Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2892Input0) = fromList transition2892Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2892 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0429 = 1 • support0199 := by
  have hs : support0429 = fromList transition2892Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2892Chunk0]
  have hn : (transition2892Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2893Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2893Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 660, 661, 662, 663, 512, 513, 514, 515]
private theorem transition2893Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2893Input0) = fromList transition2893Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2893 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0429 = 1 • support1745 := by
  have hs : support0429 = fromList transition2893Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2893Chunk0]
  have hn : (transition2893Raw0 : Multiset ℕ) = 1 • (supportNumbers1745 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1745] using hm

private def transition2894Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2894Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2894Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2894Input0) = fromList transition2894Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2894 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0429 = 1 • support0199 := by
  have hs : support0429 = fromList transition2894Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2894Chunk0]
  have hn : (transition2894Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2895Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2895Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 564, 565, 566, 567, 672, 673, 674, 675]
private theorem transition2895Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2895Input0) = fromList transition2895Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2895 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0429 = 1 • support1746 := by
  have hs : support0429 = fromList transition2895Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2895Chunk0]
  have hn : (transition2895Raw0 : Multiset ℕ) = 1 • (supportNumbers1746 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1746] using hm

private def transition2896Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 564, 565, 566, 567, 672, 673, 674, 675]
private def transition2896Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 308, 309, 310, 311, 416, 417, 418, 419]
private theorem transition2896Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2896Input0) = fromList transition2896Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2896 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1746 = 1 • support1747 := by
  have hs : support1746 = fromList transition2896Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2896Chunk0]
  have hn : (transition2896Raw0 : Multiset ℕ) = 1 • (supportNumbers1747 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1747] using hm

private def transition2897Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 564, 565, 566, 567, 672, 673, 674, 675]
private def transition2897Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition2897Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2897Input0) = fromList transition2897Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2897 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1746 = 1 • support1748 := by
  have hs : support1746 = fromList transition2897Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2897Chunk0]
  have hn : (transition2897Raw0 : Multiset ℕ) = 1 • (supportNumbers1748 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1748] using hm

private def transition2898Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 532, 533, 534, 535, 640, 641, 642, 643, 768, 769, 770, 771, 916, 917, 918, 919]
private def transition2898Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 20, 21, 22, 23, 128, 129, 130, 131, 276, 277, 278, 279, 384, 385, 386, 387, 256, 257, 258, 259, 404, 405, 406, 407]
private theorem transition2898Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2898Input0) = fromList transition2898Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2898 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0430 = 1 • support0377 := by
  have hs : support0430 = fromList transition2898Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2898Chunk0]
  have hn : (transition2898Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2899Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 532, 533, 534, 535, 640, 641, 642, 643, 768, 769, 770, 771, 916, 917, 918, 919]
private def transition2899Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 256, 896, 257, 897, 258, 898, 259, 899, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition2899Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2899Input0) = fromList transition2899Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2899 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0430 = 1 • support0378 := by
  have hs : support0430 = fromList transition2899Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2899Chunk0]
  have hn : (transition2899Raw0 : Multiset ℕ) = 1 • (supportNumbers0378 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0378] using hm

private def transition2900Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 532, 533, 534, 535, 640, 641, 642, 643, 768, 769, 770, 771, 916, 917, 918, 919]
private def transition2900Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 20, 21, 22, 23, 128, 129, 130, 131, 276, 277, 278, 279, 384, 385, 386, 387, 256, 257, 258, 259, 404, 405, 406, 407]
private theorem transition2900Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2900Input0) = fromList transition2900Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2900 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0430 = 1 • support0377 := by
  have hs : support0430 = fromList transition2900Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2900Chunk0]
  have hn : (transition2900Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2901Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 532, 533, 534, 535, 640, 641, 642, 643, 768, 769, 770, 771, 916, 917, 918, 919]
private def transition2901Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 256, 800, 257, 801, 258, 802, 259, 803, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition2901Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2901Input0) = fromList transition2901Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2901 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0430 = 1 • support1553 := by
  have hs : support0430 = fromList transition2901Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2901Chunk0]
  have hn : (transition2901Raw0 : Multiset ℕ) = 1 • (supportNumbers1553 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1553] using hm

private def transition2902Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 520, 521, 522, 523, 668, 669, 670, 671]
private def transition2902Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private theorem transition2902Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2902Input0) = fromList transition2902Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2902 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0431 = 1 • support0461 := by
  have hs : support0431 = fromList transition2902Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2902Chunk0]
  have hn : (transition2902Raw0 : Multiset ℕ) = 1 • (supportNumbers0461 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0461] using hm

private def transition2903Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 520, 521, 522, 523, 668, 669, 670, 671]
private def transition2903Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 264, 904, 265, 905, 266, 906, 267, 907, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2903Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2903Input0) = fromList transition2903Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2903 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0431 = 1 • support0462 := by
  have hs : support0431 = fromList transition2903Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2903Chunk0]
  have hn : (transition2903Raw0 : Multiset ℕ) = 1 • (supportNumbers0462 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0462] using hm

private def transition2904Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 520, 521, 522, 523, 668, 669, 670, 671]
private def transition2904Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private theorem transition2904Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2904Input0) = fromList transition2904Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2904 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0431 = 1 • support0461 := by
  have hs : support0431 = fromList transition2904Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2904Chunk0]
  have hn : (transition2904Raw0 : Multiset ℕ) = 1 • (supportNumbers0461 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0461] using hm

private def transition2905Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition2905Raw0 : List ℕ := [0, 1, 148, 149, 10, 11, 158, 159]
private theorem transition2905Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2905Input0) = fromList transition2905Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2905 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0461 = 1 • support1750 := by
  have hs : support0461 = fromList transition2905Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2905Chunk0]
  have hn : (transition2905Raw0 : Multiset ℕ) = 1 • (supportNumbers1750 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1750] using hm

private def transition2906Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415]
private def transition2906Raw0 : List ℕ := [0, 1, 578, 579, 148, 149, 726, 727, 584, 585, 10, 11, 732, 733, 158, 159]
private theorem transition2906Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2906Input0) = fromList transition2906Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2906 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0461 = 1 • support1751 := by
  have hs : support0461 = fromList transition2906Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2906Chunk0]
  have hn : (transition2906Raw0 : Multiset ℕ) = 1 • (supportNumbers1751 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1751] using hm

private def transition2907Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 520, 521, 522, 523, 668, 669, 670, 671]
private def transition2907Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 264, 808, 265, 809, 266, 810, 267, 811, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2907Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2907Input0) = fromList transition2907Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2907 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0431 = 1 • support1753 := by
  have hs : support0431 = fromList transition2907Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2907Chunk0]
  have hn : (transition2907Raw0 : Multiset ℕ) = 1 • (supportNumbers1753 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1753] using hm

private def transition2908Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 544, 545, 546, 547, 692, 693, 694, 695, 808, 809, 810, 811, 956, 957, 958, 959]
private def transition2908Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159, 288, 289, 290, 291, 436, 437, 438, 439, 296, 297, 298, 299, 444, 445, 446, 447]
private theorem transition2908Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2908Input0) = fromList transition2908Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2908 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1753 = 1 • support1116 := by
  have hs : support1753 = fromList transition2908Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2908Chunk0]
  have hn : (transition2908Raw0 : Multiset ℕ) = 1 • (supportNumbers1116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1116] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
