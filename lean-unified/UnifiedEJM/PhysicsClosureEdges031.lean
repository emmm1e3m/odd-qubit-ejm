import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0537Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0537Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0537Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0537Input0) = fromList transition0537Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0537 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0877 = 1 • support0880 := by
  have hs : support0877 = fromList transition0537Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0537Chunk0]
  have hn : (transition0537Raw0 : Multiset ℕ) = 1 • (supportNumbers0880 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0880] using hm

private def transition0538Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 904, 905, 906, 907, 916, 917, 918, 919]
private def transition0538Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 8, 9, 10, 11, 20, 21, 22, 23, 128, 129, 130, 131, 156, 157, 158, 159, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition0538Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0538Input0) = fromList transition0538Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0538 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0068 = 1 • support0036 := by
  have hs : support0068 = fromList transition0538Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0538Chunk0]
  have hn : (transition0538Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0539Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 904, 905, 906, 907, 916, 917, 918, 919]
private def transition0539Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 156, 540, 157, 541, 158, 542, 159, 543, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition0539Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0539Input0) = fromList transition0539Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0539 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0068 = 1 • support0037 := by
  have hs : support0068 = fromList transition0539Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0539Chunk0]
  have hn : (transition0539Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition0540Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 904, 905, 906, 907, 916, 917, 918, 919]
private def transition0540Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 8, 9, 10, 11, 20, 21, 22, 23, 128, 129, 130, 131, 156, 157, 158, 159, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition0540Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0540Input0) = fromList transition0540Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0540 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0068 = 1 • support0036 := by
  have hs : support0068 = fromList transition0540Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0540Chunk0]
  have hn : (transition0540Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0541Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 264, 265, 266, 267, 276, 277, 278, 279, 384, 385, 386, 387, 412, 413, 414, 415, 520, 521, 522, 523, 532, 533, 534, 535, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799, 904, 905, 906, 907, 916, 917, 918, 919]
private def transition0541Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 156, 700, 157, 701, 158, 702, 159, 703, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition0541Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0541Input0) = fromList transition0541Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0541 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0068 = 1 • support0593 := by
  have hs : support0068 = fromList transition0541Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0541Chunk0]
  have hn : (transition0541Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition0542Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0542Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0542Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0542Input0) = fromList transition0542Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0542 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0542Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0542Chunk0]
  have hn : (transition0542Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0543Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0543Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0543Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0543Input0) = fromList transition0543Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0543 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0543Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0543Chunk0]
  have hn : (transition0543Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0544Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0544Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0544Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0544Input0) = fromList transition0544Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0544 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0544Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0544Chunk0]
  have hn : (transition0544Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0545Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0545Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0545Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0545Input0) = fromList transition0545Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0545 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0545Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0545Chunk0]
  have hn : (transition0545Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0546Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0546Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition0546Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0546Input0) = fromList transition0546Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0546 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0069 = 1 • support0069 := by
  have hs : support0069 = fromList transition0546Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0546Chunk0]
  have hn : (transition0546Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition0547Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private def transition0547Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599]
private theorem transition0547Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0547Input0) = fromList transition0547Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0547 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0069 = 1 • support0882 := by
  have hs : support0069 = fromList transition0547Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0547Chunk0]
  have hn : (transition0547Raw0 : Multiset ℕ) = 1 • (supportNumbers0882 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0882] using hm

private def transition0548Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543]
private def transition0548Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private theorem transition0548Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0548Input0) = fromList transition0548Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0548 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0070 = 1 • support0125 := by
  have hs : support0070 = fromList transition0548Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0548Chunk0]
  have hn : (transition0548Raw0 : Multiset ℕ) = 1 • (supportNumbers0125 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0125] using hm

private def transition0549Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543]
private def transition0549Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition0549Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0549Input0) = fromList transition0549Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0549 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0070 = 1 • support0126 := by
  have hs : support0070 = fromList transition0549Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0549Chunk0]
  have hn : (transition0549Raw0 : Multiset ℕ) = 1 • (supportNumbers0126 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0126] using hm

private def transition0550Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543]
private def transition0550Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private theorem transition0550Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0550Input0) = fromList transition0550Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0550 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0070 = 1 • support0125 := by
  have hs : support0070 = fromList transition0550Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0550Chunk0]
  have hn : (transition0550Raw0 : Multiset ℕ) = 1 • (supportNumbers0125 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0125] using hm

private def transition0551Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0551Raw0 : List ℕ := [0, 1, 20, 21, 10, 11, 30, 31]
private theorem transition0551Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0551Input0) = fromList transition0551Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0551 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0125 = 1 • support0884 := by
  have hs : support0125 = fromList transition0551Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0551Chunk0]
  have hn : (transition0551Raw0 : Multiset ℕ) = 1 • (supportNumbers0884 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0884] using hm

private def transition0552Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287]
private def transition0552Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 584, 585, 10, 11, 604, 605, 30, 31]
private theorem transition0552Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0552Input0) = fromList transition0552Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0552 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0125 = 1 • support0886 := by
  have hs : support0125 = fromList transition0552Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0552Chunk0]
  have hn : (transition0552Raw0 : Multiset ℕ) = 1 • (supportNumbers0886 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0886] using hm

private def transition0553Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543]
private def transition0553Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition0553Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0553Input0) = fromList transition0553Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0553 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0070 = 1 • support0888 := by
  have hs : support0070 = fromList transition0553Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0553Chunk0]
  have hn : (transition0553Raw0 : Multiset ℕ) = 1 • (supportNumbers0888 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0888] using hm

private def transition0554Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 544, 545, 546, 547, 564, 565, 566, 567, 808, 809, 810, 811, 828, 829, 830, 831]
private def transition0554Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31, 288, 289, 290, 291, 308, 309, 310, 311, 296, 297, 298, 299, 316, 317, 318, 319]
private theorem transition0554Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0554Input0) = fromList transition0554Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0554 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0888 = 1 • support0889 := by
  have hs : support0888 = fromList transition0554Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0554Chunk0]
  have hn : (transition0554Raw0 : Multiset ℕ) = 1 • (supportNumbers0889 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0889] using hm

private def transition0555Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 544, 545, 546, 547, 564, 565, 566, 567, 808, 809, 810, 811, 828, 829, 830, 831]
private def transition0555Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 8, 584, 9, 585, 10, 586, 11, 587, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition0555Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0555Input0) = fromList transition0555Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0555 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0888 = 1 • support0890 := by
  have hs : support0888 = fromList transition0555Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0555Chunk0]
  have hn : (transition0555Raw0 : Multiset ℕ) = 1 • (supportNumbers0890 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0890] using hm

private def transition0556Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0556Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0556Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0556Input0) = fromList transition0556Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0556 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0071 = 1 • support0034 := by
  have hs : support0071 = fromList transition0556Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0556Chunk0]
  have hn : (transition0556Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition0557Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0557Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0557Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0557Input0) = fromList transition0557Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0557 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0071 = 1 • support0127 := by
  have hs : support0071 = fromList transition0557Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0557Chunk0]
  have hn : (transition0557Raw0 : Multiset ℕ) = 1 • (supportNumbers0127 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0127] using hm

private def transition0558Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0558Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0558Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0558Input0) = fromList transition0558Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0558 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0071 = 1 • support0034 := by
  have hs : support0071 = fromList transition0558Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0558Chunk0]
  have hn : (transition0558Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition0559Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0559Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 680, 681, 682, 683, 700, 701, 702, 703, 544, 545, 546, 547, 564, 565, 566, 567, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition0559Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0559Input0) = fromList transition0559Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0559 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0071 = 1 • support0892 := by
  have hs : support0071 = fromList transition0559Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0559Chunk0]
  have hn : (transition0559Raw0 : Multiset ℕ) = 1 • (supportNumbers0892 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0892] using hm

private def transition0560Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0560Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition0560Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0560Input0) = fromList transition0560Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0560 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0892 = 1 • support0712 := by
  have hs : support0892 = fromList transition0560Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0560Chunk0]
  have hn : (transition0560Raw0 : Multiset ℕ) = 1 • (supportNumbers0712 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0712] using hm

private def transition0561Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 544, 545, 546, 547, 564, 565, 566, 567, 680, 681, 682, 683, 700, 701, 702, 703]
private def transition0561Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0561Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0561Input0) = fromList transition0561Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0561 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0892 = 1 • support0714 := by
  have hs : support0892 = fromList transition0561Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0561Chunk0]
  have hn : (transition0561Raw0 : Multiset ℕ) = 1 • (supportNumbers0714 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0714] using hm

private def transition0562Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition0562Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition0562Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0562Input0) = fromList transition0562Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0562 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0072 = 2 • support0128 := by
  have hs : support0072 = fromList transition0562Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0562Chunk0]
  have hn : (transition0562Raw0 : Multiset ℕ) = 2 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0563Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition0563Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition0563Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0563Input0) = fromList transition0563Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0563 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0072 = 2 • support0129 := by
  have hs : support0072 = fromList transition0563Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0563Chunk0]
  have hn : (transition0563Raw0 : Multiset ℕ) = 2 • (supportNumbers0129 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0129] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
