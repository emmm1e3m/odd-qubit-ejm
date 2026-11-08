import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0960Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 640, 641, 642, 643, 660, 661, 662, 663, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0960Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31, 384, 385, 386, 387, 404, 405, 406, 407, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0960Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0960Input0) = fromList transition0960Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0960 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0126 = 1 • support0014 := by
  have hs : support0126 = fromList transition0960Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0960Chunk0]
  have hn : (transition0960Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition0961Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 640, 641, 642, 643, 660, 661, 662, 663, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0961Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 8, 648, 9, 649, 10, 650, 11, 651, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0961Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0961Input0) = fromList transition0961Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0961 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0126 = 1 • support0015 := by
  have hs : support0126 = fromList transition0961Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0961Chunk0]
  have hn : (transition0961Raw0 : Multiset ℕ) = 1 • (supportNumbers0015 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0015] using hm

private def transition0962Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 640, 641, 642, 643, 660, 661, 662, 663, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0962Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31, 384, 385, 386, 387, 404, 405, 406, 407, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0962Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0962Input0) = fromList transition0962Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0962 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0126 = 1 • support0014 := by
  have hs : support0126 = fromList transition0962Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0962Chunk0]
  have hn : (transition0962Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition0963Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 264, 265, 266, 267, 284, 285, 286, 287, 640, 641, 642, 643, 660, 661, 662, 663, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0963Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 8, 552, 9, 553, 10, 554, 11, 555, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0963Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0963Input0) = fromList transition0963Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0963 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0126 = 1 • support0505 := by
  have hs : support0126 = fromList transition0963Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0963Chunk0]
  have hn : (transition0963Raw0 : Multiset ℕ) = 1 • (supportNumbers0505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0505] using hm

private def transition0964Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition0964Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition0964Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0964Input0) = fromList transition0964Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0964 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0127 = 1 • support0128 := by
  have hs : support0127 = fromList transition0964Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0964Chunk0]
  have hn : (transition0964Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0965Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition0965Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition0965Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0965Input0) = fromList transition0965Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0965 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0127 = 1 • support0129 := by
  have hs : support0127 = fromList transition0965Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0965Chunk0]
  have hn : (transition0965Raw0 : Multiset ℕ) = 1 • (supportNumbers0129 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0129] using hm

private def transition0966Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition0966Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition0966Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0966Input0) = fromList transition0966Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0966 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0127 = 1 • support0128 := by
  have hs : support0127 = fromList transition0966Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0966Chunk0]
  have hn : (transition0966Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition0967Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition0967Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition0967Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0967Input0) = fromList transition0967Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0967 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0127 = 1 • support0896 := by
  have hs : support0127 = fromList transition0967Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0967Chunk0]
  have hn : (transition0967Raw0 : Multiset ℕ) = 1 • (supportNumbers0896 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0896] using hm

private def transition0968Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0968Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0968Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0968Input0) = fromList transition0968Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0968 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0128 = 1 • support0204 := by
  have hs : support0128 = fromList transition0968Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0968Chunk0]
  have hn : (transition0968Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0969Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0969Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 520, 521, 522, 523, 540, 541, 542, 543, 8, 9, 10, 11, 28, 29, 30, 31, 512, 513, 514, 515, 532, 533, 534, 535]
private theorem transition0969Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0969Input0) = fromList transition0969Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0969 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0128 = 1 • support0205 := by
  have hs : support0128 = fromList transition0969Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0969Chunk0]
  have hn : (transition0969Raw0 : Multiset ℕ) = 1 • (supportNumbers0205 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0205] using hm

private def transition0970Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0970Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition0970Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0970Input0) = fromList transition0970Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0970 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0128 = 1 • support0204 := by
  have hs : support0128 = fromList transition0970Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0970Chunk0]
  have hn : (transition0970Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition0971Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition0971Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 680, 681, 682, 683, 700, 701, 702, 703, 8, 9, 10, 11, 28, 29, 30, 31, 672, 673, 674, 675, 692, 693, 694, 695]
private theorem transition0971Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0971Input0) = fromList transition0971Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0971 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0128 = 1 • support1129 := by
  have hs : support0128 = fromList transition0971Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0971Chunk0]
  have hn : (transition0971Raw0 : Multiset ℕ) = 1 • (supportNumbers1129 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1129] using hm

private def transition0972Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition0972Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 416, 417, 418, 419, 424, 425, 426, 427, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition0972Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0972Input0) = fromList transition0972Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0972 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1129 = 1 • support1130 := by
  have hs : support1129 = fromList transition0972Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0972Chunk0]
  have hn : (transition0972Raw0 : Multiset ℕ) = 1 • (supportNumbers1130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1130] using hm

private def transition0973Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition0973Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0973Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0973Input0) = fromList transition0973Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0973 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1129 = 1 • support1131 := by
  have hs : support1129 = fromList transition0973Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0973Chunk0]
  have hn : (transition0973Raw0 : Multiset ℕ) = 1 • (supportNumbers1131 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1131] using hm

private def transition0974Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0974Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 8, 9, 10, 11, 28, 29, 30, 31, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0974Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0974Input0) = fromList transition0974Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0974 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0129 = 1 • support0036 := by
  have hs : support0129 = fromList transition0974Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0974Chunk0]
  have hn : (transition0974Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0975Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0975Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 8, 648, 9, 649, 10, 650, 11, 651, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0975Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0975Input0) = fromList transition0975Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0975 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0129 = 1 • support0037 := by
  have hs : support0129 = fromList transition0975Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0975Chunk0]
  have hn : (transition0975Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition0976Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0976Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 8, 9, 10, 11, 28, 29, 30, 31, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0976Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0976Input0) = fromList transition0976Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0976 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0129 = 1 • support0036 := by
  have hs : support0129 = fromList transition0976Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0976Chunk0]
  have hn : (transition0976Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0977Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 264, 265, 266, 267, 284, 285, 286, 287, 384, 385, 386, 387, 404, 405, 406, 407, 520, 521, 522, 523, 540, 541, 542, 543, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition0977Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 8, 552, 9, 553, 10, 554, 11, 555, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0977Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0977Input0) = fromList transition0977Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0977 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0129 = 1 • support0593 := by
  have hs : support0129 = fromList transition0977Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0977Chunk0]
  have hn : (transition0977Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition0978Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0978Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0978Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0978Input0) = fromList transition0978Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0978 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition0978Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0978Chunk0]
  have hn : (transition0978Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0979Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0979Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0979Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0979Input0) = fromList transition0979Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0979 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition0979Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0979Chunk0]
  have hn : (transition0979Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0980Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0980Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0980Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0980Input0) = fromList transition0980Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0980 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition0980Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0980Chunk0]
  have hn : (transition0980Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0981Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0981Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0981Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0981Input0) = fromList transition0981Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0981 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition0981Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0981Chunk0]
  have hn : (transition0981Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0982Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0982Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition0982Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0982Input0) = fromList transition0982Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0982 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition0982Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0982Chunk0]
  have hn : (transition0982Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition0983Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition0983Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727]
private theorem transition0983Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0983Input0) = fromList transition0983Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0983 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0130 = 1 • support1133 := by
  have hs : support0130 = fromList transition0983Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0983Chunk0]
  have hn : (transition0983Raw0 : Multiset ℕ) = 1 • (supportNumbers1133 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1133] using hm

private def transition0984Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 520, 521, 522, 523, 540, 541, 542, 543, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0984Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0984Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0984Input0) = fromList transition0984Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0984 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0131 = 1 • support0206 := by
  have hs : support0131 = fromList transition0984Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0984Chunk0]
  have hn : (transition0984Raw0 : Multiset ℕ) = 1 • (supportNumbers0206 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0206] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
