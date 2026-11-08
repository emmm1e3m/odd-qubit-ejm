import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0587Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition0587Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition0587Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0587Input0) = fromList transition0587Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0587 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0075 = 1 • support0909 := by
  have hs : support0075 = fromList transition0587Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0587Chunk0]
  have hn : (transition0587Raw0 : Multiset ℕ) = 1 • (supportNumbers0909 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0909] using hm

private def transition0588Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition0588Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition0588Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0588Input0) = fromList transition0588Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0588 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0909 = 1 • support0910 := by
  have hs : support0909 = fromList transition0588Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0588Chunk0]
  have hn : (transition0588Raw0 : Multiset ℕ) = 1 • (supportNumbers0910 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0910] using hm

private def transition0589Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition0589Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition0589Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0589Input0) = fromList transition0589Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0589 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0909 = 1 • support0912 := by
  have hs : support0909 = fromList transition0589Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0589Chunk0]
  have hn : (transition0589Raw0 : Multiset ℕ) = 1 • (supportNumbers0912 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0912] using hm

private def transition0590Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0590Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0590Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0590Input0) = fromList transition0590Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0590 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0076 = 1 • support0016 := by
  have hs : support0076 = fromList transition0590Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0590Chunk0]
  have hn : (transition0590Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0591Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0591Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591]
private theorem transition0591Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0591Input0) = fromList transition0591Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0591 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0076 = 1 • support0134 := by
  have hs : support0076 = fromList transition0591Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0591Chunk0]
  have hn : (transition0591Raw0 : Multiset ℕ) = 1 • (supportNumbers0134 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0134] using hm

private def transition0592Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0592Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0592Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0592Input0) = fromList transition0592Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0592 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0076 = 1 • support0016 := by
  have hs : support0076 = fromList transition0592Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0592Chunk0]
  have hn : (transition0592Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0593Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0593Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751]
private theorem transition0593Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0593Input0) = fromList transition0593Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0593 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0076 = 1 • support0914 := by
  have hs : support0076 = fromList transition0593Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0593Chunk0]
  have hn : (transition0593Raw0 : Multiset ℕ) = 1 • (supportNumbers0914 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0914] using hm

private def transition0594Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0594Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition0594Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0594Input0) = fromList transition0594Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0594 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0914 = 1 • support0915 := by
  have hs : support0914 = fromList transition0594Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0594Chunk0]
  have hn : (transition0594Raw0 : Multiset ℕ) = 1 • (supportNumbers0915 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0915] using hm

private def transition0595Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0595Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0595Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0595Input0) = fromList transition0595Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0595 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0914 = 1 • support0917 := by
  have hs : support0914 = fromList transition0595Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0595Chunk0]
  have hn : (transition0595Raw0 : Multiset ℕ) = 1 • (supportNumbers0917 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0917] using hm

private def transition0596Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0596Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0596Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0596Input0) = fromList transition0596Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0596 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0076 = 1 • support0076 := by
  have hs : support0076 = fromList transition0596Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0596Chunk0]
  have hn : (transition0596Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0597Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0597Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition0597Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0597Input0) = fromList transition0597Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0597 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0076 = 1 • support0135 := by
  have hs : support0076 = fromList transition0597Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0597Chunk0]
  have hn : (transition0597Raw0 : Multiset ℕ) = 1 • (supportNumbers0135 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0135] using hm

private def transition0598Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0598Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0598Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0598Input0) = fromList transition0598Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0598 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0076 = 1 • support0076 := by
  have hs : support0076 = fromList transition0598Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0598Chunk0]
  have hn : (transition0598Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0599Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0599Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751]
private theorem transition0599Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0599Input0) = fromList transition0599Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0599 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0076 = 1 • support0918 := by
  have hs : support0076 = fromList transition0599Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0599Chunk0]
  have hn : (transition0599Raw0 : Multiset ℕ) = 1 • (supportNumbers0918 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0918] using hm

private def transition0600Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0600Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition0600Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0600Input0) = fromList transition0600Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0600 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0918 = 1 • support0601 := by
  have hs : support0918 = fromList transition0600Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0600Chunk0]
  have hn : (transition0600Raw0 : Multiset ℕ) = 1 • (supportNumbers0601 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0601] using hm

private def transition0601Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0601Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0601Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0601Input0) = fromList transition0601Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0601 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0918 = 1 • support0603 := by
  have hs : support0918 = fromList transition0601Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0601Chunk0]
  have hn : (transition0601Raw0 : Multiset ℕ) = 1 • (supportNumbers0603 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0603] using hm

private def transition0602Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0602Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition0602Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0602Input0) = fromList transition0602Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0602 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0077 = 1 • support0004 := by
  have hs : support0077 = fromList transition0602Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0602Chunk0]
  have hn : (transition0602Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition0603Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0603Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591, 8, 10, 12, 14, 73, 75, 77, 79, 512, 514, 516, 518, 577, 579, 581, 583]
private theorem transition0603Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0603Input0) = fromList transition0603Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0603 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0077 = 1 • support0136 := by
  have hs : support0077 = fromList transition0603Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0603Chunk0]
  have hn : (transition0603Raw0 : Multiset ℕ) = 1 • (supportNumbers0136 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0136] using hm

private def transition0604Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0604Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79]
private theorem transition0604Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0604Input0) = fromList transition0604Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0604 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0077 = 1 • support0004 := by
  have hs : support0077 = fromList transition0604Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0604Chunk0]
  have hn : (transition0604Raw0 : Multiset ℕ) = 1 • (supportNumbers0004 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0004] using hm

private def transition0605Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0605Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77]
private theorem transition0605Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0605Input0) = fromList transition0605Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0605 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0004 = 1 • support0919 := by
  have hs : support0004 = fromList transition0605Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0605Chunk0]
  have hn : (transition0605Raw0 : Multiset ℕ) = 1 • (supportNumbers0919 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0919] using hm

private def transition0606Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79]
private def transition0606Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527]
private theorem transition0606Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0606Input0) = fromList transition0606Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0606 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0004 = 1 • support0921 := by
  have hs : support0004 = fromList transition0606Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0606Chunk0]
  have hn : (transition0606Raw0 : Multiset ℕ) = 1 • (supportNumbers0921 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0921] using hm

private def transition0607Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0607Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 680, 682, 684, 686, 745, 747, 749, 751, 8, 10, 12, 14, 73, 75, 77, 79, 672, 674, 676, 678, 737, 739, 741, 743]
private theorem transition0607Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0607Input0) = fromList transition0607Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0607 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0077 = 1 • support0923 := by
  have hs : support0077 = fromList transition0607Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0607Chunk0]
  have hn : (transition0607Raw0 : Multiset ℕ) = 1 • (supportNumbers0923 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0923] using hm

private def transition0608Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition0608Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private theorem transition0608Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0608Input0) = fromList transition0608Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0608 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0923 = 1 • support0924 := by
  have hs : support0923 = fromList transition0608Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0608Chunk0]
  have hn : (transition0608Raw0 : Multiset ℕ) = 1 • (supportNumbers0924 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0924] using hm

private def transition0609Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 672, 674, 676, 678, 680, 682, 684, 686, 737, 739, 741, 743, 745, 747, 749, 751]
private def transition0609Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 8, 584, 10, 586, 12, 588, 14, 590, 65, 513, 67, 515, 69, 517, 71, 519, 73, 521, 75, 523, 77, 525, 79, 527, 416, 992, 418, 994, 420, 996, 422, 998, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 481, 929, 483, 931, 485, 933, 487, 935, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0609Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0609Input0) = fromList transition0609Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0609 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0923 = 1 • support0926 := by
  have hs : support0923 = fromList transition0609Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0609Chunk0]
  have hn : (transition0609Raw0 : Multiset ℕ) = 1 • (supportNumbers0926 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0926] using hm

private def transition0610Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition0610Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 8, 10, 12, 14, 73, 75, 77, 79, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0610Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0610Input0) = fromList transition0610Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0610 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0078 = 1 • support0137 := by
  have hs : support0078 = fromList transition0610Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0610Chunk0]
  have hn : (transition0610Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition0611Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition0611Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 8, 648, 10, 650, 12, 652, 14, 654, 73, 713, 75, 715, 77, 717, 79, 719, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition0611Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0611Input0) = fromList transition0611Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0611 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0078 = 1 • support0138 := by
  have hs : support0078 = fromList transition0611Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0611Chunk0]
  have hn : (transition0611Raw0 : Multiset ℕ) = 1 • (supportNumbers0138 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0138] using hm

private def transition0612Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 520, 522, 524, 526, 585, 587, 589, 591, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 904, 906, 908, 910, 969, 971, 973, 975]
private def transition0612Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 8, 10, 12, 14, 73, 75, 77, 79, 128, 130, 132, 134, 193, 195, 197, 199, 264, 266, 268, 270, 329, 331, 333, 335, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition0612Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0612Input0) = fromList transition0612Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0612 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0078 = 1 • support0137 := by
  have hs : support0078 = fromList transition0612Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0612Chunk0]
  have hn : (transition0612Raw0 : Multiset ℕ) = 1 • (supportNumbers0137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0137] using hm

private def transition0613Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0613Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 128, 132, 136, 140, 193, 197, 201, 205, 2, 6, 10, 14, 67, 71, 75, 79, 130, 134, 138, 142, 195, 199, 203, 207]
private theorem transition0613Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0613Input0) = fromList transition0613Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0613 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0137 = 1 • support0215 := by
  have hs : support0137 = fromList transition0613Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0613Chunk0]
  have hn : (transition0613Raw0 : Multiset ℕ) = 1 • (supportNumbers0215 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0215] using hm

private def transition0614Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 256, 258, 260, 262, 264, 266, 268, 270, 321, 323, 325, 327, 329, 331, 333, 335, 384, 386, 388, 390, 392, 394, 396, 398, 449, 451, 453, 455, 457, 459, 461, 463]
private def transition0614Raw0 : List ℕ := [0, 578, 4, 582, 8, 586, 12, 590, 65, 515, 69, 519, 73, 523, 77, 527, 128, 706, 132, 710, 136, 714, 140, 718, 193, 643, 197, 647, 201, 651, 205, 655, 576, 2, 580, 6, 584, 10, 588, 14, 513, 67, 517, 71, 521, 75, 525, 79, 704, 130, 708, 134, 712, 138, 716, 142, 641, 195, 645, 199, 649, 203, 653, 207]
private theorem transition0614Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0614Input0) = fromList transition0614Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0614 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0137 = 1 • support0929 := by
  have hs : support0137 = fromList transition0614Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0614Chunk0]
  have hn : (transition0614Raw0 : Multiset ℕ) = 1 • (supportNumbers0929 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0929] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
