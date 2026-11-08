import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3079Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 532, 533, 534, 535, 640, 641, 642, 643, 796, 797, 798, 799, 904, 905, 906, 907]
private def transition3079Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 8, 648, 9, 649, 10, 650, 11, 651, 156, 540, 157, 541, 158, 542, 159, 543, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition3079Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3079Input0) = fromList transition3079Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3079 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0462 = 1 • support0289 := by
  have hs : support0462 = fromList transition3079Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3079Chunk0]
  have hn : (transition3079Raw0 : Multiset ℕ) = 1 • (supportNumbers0289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0289] using hm

private def transition3080Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 532, 533, 534, 535, 640, 641, 642, 643, 796, 797, 798, 799, 904, 905, 906, 907]
private def transition3080Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159, 276, 277, 278, 279, 384, 385, 386, 387, 284, 285, 286, 287, 392, 393, 394, 395]
private theorem transition3080Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3080Input0) = fromList transition3080Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3080 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0462 = 1 • support0288 := by
  have hs : support0462 = fromList transition3080Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3080Chunk0]
  have hn : (transition3080Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition3081Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 264, 265, 266, 267, 412, 413, 414, 415, 532, 533, 534, 535, 640, 641, 642, 643, 796, 797, 798, 799, 904, 905, 906, 907]
private def transition3081Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 8, 552, 9, 553, 10, 554, 11, 555, 156, 700, 157, 701, 158, 702, 159, 703, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition3081Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3081Input0) = fromList transition3081Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3081 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0462 = 1 • support1355 := by
  have hs : support0462 = fromList transition3081Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3081Chunk0]
  have hn : (transition3081Raw0 : Multiset ℕ) = 1 • (supportNumbers1355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1355] using hm

private def transition3082Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590]
private def transition3082Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private theorem transition3082Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3082Input0) = fromList transition3082Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3082 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0463 = 1 • support0474 := by
  have hs : support0463 = fromList transition3082Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3082Chunk0]
  have hn : (transition3082Raw0 : Multiset ℕ) = 1 • (supportNumbers0474 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0474] using hm

private def transition3083Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590]
private def transition3083Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974]
private theorem transition3083Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3083Input0) = fromList transition3083Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3083 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0463 = 1 • support0475 := by
  have hs : support0463 = fromList transition3083Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3083Chunk0]
  have hn : (transition3083Raw0 : Multiset ℕ) = 1 • (supportNumbers0475 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0475] using hm

private def transition3084Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590]
private def transition3084Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private theorem transition3084Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3084Input0) = fromList transition3084Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3084 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0463 = 1 • support0474 := by
  have hs : support0463 = fromList transition3084Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3084Chunk0]
  have hn : (transition3084Raw0 : Multiset ℕ) = 1 • (supportNumbers0474 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0474] using hm

private def transition3085Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3085Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 2, 6, 11, 15, 67, 71, 74, 78]
private theorem transition3085Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3085Input0) = fromList transition3085Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3085 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0474 = 1 • support0217 := by
  have hs : support0474 = fromList transition3085Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3085Chunk0]
  have hn : (transition3085Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition3086Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private def transition3086Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 576, 2, 580, 6, 585, 11, 589, 15, 513, 67, 517, 71, 520, 74, 524, 78]
private theorem transition3086Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3086Input0) = fromList transition3086Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3086 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0474 = 1 • support0310 := by
  have hs : support0474 = fromList transition3086Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3086Chunk0]
  have hn : (transition3086Raw0 : Multiset ℕ) = 1 • (supportNumbers0310 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0310] using hm

private def transition3087Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590]
private def transition3087Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878]
private theorem transition3087Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3087Input0) = fromList transition3087Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3087 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0463 = 1 • support1774 := by
  have hs : support0463 = fromList transition3087Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3087Chunk0]
  have hn : (transition3087Raw0 : Multiset ℕ) = 1 • (supportNumbers1774 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1774] using hm

private def transition3088Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878]
private def transition3088Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366]
private theorem transition3088Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3088Input0) = fromList transition3088Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3088 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1774 = 2 • support0935 := by
  have hs : support1774 = fromList transition3088Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3088Chunk0]
  have hn : (transition3088Raw0 : Multiset ℕ) = 2 • (supportNumbers0935 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0935] using hm

private def transition3089Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878]
private def transition3089Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814]
private theorem transition3089Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3089Input0) = fromList transition3089Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3089 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1774 = 2 • support0937 := by
  have hs : support1774 = fromList transition3089Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3089Chunk0]
  have hn : (transition3089Raw0 : Multiset ℕ) = 2 • (supportNumbers0937 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0937] using hm

private def transition3090Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition3090Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition3090Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3090Input0) = fromList transition3090Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3090 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0464 = 1 • support0388 := by
  have hs : support0464 = fromList transition3090Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3090Chunk0]
  have hn : (transition3090Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition3091Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition3091Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition3091Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3091Input0) = fromList transition3091Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3091 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0464 = 1 • support0388 := by
  have hs : support0464 = fromList transition3091Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3091Chunk0]
  have hn : (transition3091Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition3092Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition3092Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition3092Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3092Input0) = fromList transition3092Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3092 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0464 = 1 • support0388 := by
  have hs : support0464 = fromList transition3092Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3092Chunk0]
  have hn : (transition3092Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition3093Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition3093Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition3093Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3093Input0) = fromList transition3093Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3093 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0464 = 1 • support0388 := by
  have hs : support0464 = fromList transition3093Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3093Chunk0]
  have hn : (transition3093Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition3094Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition3094Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition3094Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition3094Input0) = fromList transition3094Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3094 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0388 = 1 • support0388 := by
  have hs : support0388 = fromList transition3094Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3094Chunk0]
  have hn : (transition3094Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition3095Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private def transition3095Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 128, 704, 130, 706, 132, 708, 134, 710, 137, 713, 139, 715, 141, 717, 143, 719, 193, 641, 195, 643, 197, 645, 199, 647, 200, 648, 202, 650, 204, 652, 206, 654]
private theorem transition3095Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition3095Input0) = fromList transition3095Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3095 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0388 = 1 • support1396 := by
  have hs : support0388 = fromList transition3095Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3095Chunk0]
  have hn : (transition3095Raw0 : Multiset ℕ) = 1 • (supportNumbers1396 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1396] using hm

private def transition3096Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition3096Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition3096Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3096Input0) = fromList transition3096Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3096 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0465 = 1 • support0308 := by
  have hs : support0465 = fromList transition3096Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3096Chunk0]
  have hn : (transition3096Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition3097Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition3097Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 9, 649, 11, 651, 13, 653, 15, 655, 72, 712, 74, 714, 76, 716, 78, 718, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition3097Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3097Input0) = fromList transition3097Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3097 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0465 = 1 • support0309 := by
  have hs : support0465 = fromList transition3097Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3097Chunk0]
  have hn : (transition3097Raw0 : Multiset ℕ) = 1 • (supportNumbers0309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0309] using hm

private def transition3098Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition3098Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition3098Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3098Input0) = fromList transition3098Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3098 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0465 = 1 • support0308 := by
  have hs : support0465 = fromList transition3098Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3098Chunk0]
  have hn : (transition3098Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
