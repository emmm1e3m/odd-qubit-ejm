import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2601Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2601Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition2601Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2601Input0) = fromList transition2601Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2601 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0378 = 2 • support0378 := by
  have hs : support0378 = fromList transition2601Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2601Chunk0]
  have hn : (transition2601Raw0 : Multiset ℕ) = 2 • (supportNumbers0378 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0378] using hm

private def transition2602Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2602Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2602Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2602Input0) = fromList transition2602Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2602 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0378 = 2 • support0377 := by
  have hs : support0378 = fromList transition2602Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2602Chunk0]
  have hn : (transition2602Raw0 : Multiset ℕ) = 2 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2603Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2603Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition2603Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2603Input0) = fromList transition2603Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2603 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0378 = 2 • support1553 := by
  have hs : support0378 = fromList transition2603Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2603Chunk0]
  have hn : (transition2603Raw0 : Multiset ℕ) = 2 • (supportNumbers1553 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1553] using hm

private def transition2604Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2604Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2604Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2604Input0) = fromList transition2604Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2604 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0379 = 1 • support0034 := by
  have hs : support0379 = fromList transition2604Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2604Chunk0]
  have hn : (transition2604Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2605Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2605Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2605Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2605Input0) = fromList transition2605Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2605 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0379 = 1 • support0034 := by
  have hs : support0379 = fromList transition2605Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2605Chunk0]
  have hn : (transition2605Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2606Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2606Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2606Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2606Input0) = fromList transition2606Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2606 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0379 = 1 • support0034 := by
  have hs : support0379 = fromList transition2606Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2606Chunk0]
  have hn : (transition2606Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2607Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition2607Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2607Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2607Input0) = fromList transition2607Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2607 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0379 = 1 • support0034 := by
  have hs : support0379 = fromList transition2607Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2607Chunk0]
  have hn : (transition2607Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2608Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2608Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition2608Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2608Input0) = fromList transition2608Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2608 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0034 = 1 • support0034 := by
  have hs : support0034 = fromList transition2608Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2608Chunk0]
  have hn : (transition2608Raw0 : Multiset ℕ) = 1 • (supportNumbers0034 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0034] using hm

private def transition2609Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159]
private def transition2609Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition2609Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2609Input0) = fromList transition2609Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2609 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0034 = 1 • support0709 := by
  have hs : support0034 = fromList transition2609Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2609Chunk0]
  have hn : (transition2609Raw0 : Multiset ℕ) = 1 • (supportNumbers0709 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0709] using hm

private def transition2610Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799]
private def transition2610Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287]
private theorem transition2610Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2610Input0) = fromList transition2610Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2610 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0380 = 1 • support0128 := by
  have hs : support0380 = fromList transition2610Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2610Chunk0]
  have hn : (transition2610Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition2611Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799]
private def transition2611Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition2611Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2611Input0) = fromList transition2611Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2611 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0380 = 1 • support0129 := by
  have hs : support0380 = fromList transition2611Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2611Chunk0]
  have hn : (transition2611Raw0 : Multiset ℕ) = 1 • (supportNumbers0129 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0129] using hm

private def transition2612Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799]
private def transition2612Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287]
private theorem transition2612Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2612Input0) = fromList transition2612Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2612 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0380 = 1 • support0128 := by
  have hs : support0380 = fromList transition2612Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2612Chunk0]
  have hn : (transition2612Raw0 : Multiset ℕ) = 1 • (supportNumbers0128 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0128] using hm

private def transition2613Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799]
private def transition2613Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition2613Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2613Input0) = fromList transition2613Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2613 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0380 = 1 • support0896 := by
  have hs : support0380 = fromList transition2613Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2613Chunk0]
  have hn : (transition2613Raw0 : Multiset ℕ) = 1 • (supportNumbers0896 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0896] using hm

private def transition2614Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2614Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2614Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2614Input0) = fromList transition2614Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2614 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2614Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2614Chunk0]
  have hn : (transition2614Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2615Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2615Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583]
private theorem transition2615Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2615Input0) = fromList transition2615Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2615 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0299 = 1 • support0300 := by
  have hs : support0299 = fromList transition2615Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2615Chunk0]
  have hn : (transition2615Raw0 : Multiset ℕ) = 1 • (supportNumbers0300 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0300] using hm

private def transition2616Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2616Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition2616Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2616Input0) = fromList transition2616Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2616 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0299 = 1 • support0299 := by
  have hs : support0299 = fromList transition2616Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2616Chunk0]
  have hn : (transition2616Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition2617Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition2617Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743]
private theorem transition2617Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2617Input0) = fromList transition2617Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2617 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0299 = 1 • support1376 := by
  have hs : support0299 = fromList transition2617Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2617Chunk0]
  have hn : (transition2617Raw0 : Multiset ℕ) = 1 • (supportNumbers1376 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1376] using hm

private def transition2618Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 512, 514, 516, 518, 577, 579, 581, 583, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2618Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2618Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2618Input0) = fromList transition2618Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2618 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0381 = 1 • support0437 := by
  have hs : support0381 = fromList transition2618Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2618Chunk0]
  have hn : (transition2618Raw0 : Multiset ℕ) = 1 • (supportNumbers0437 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0437] using hm

private def transition2619Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 512, 514, 516, 518, 577, 579, 581, 583, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2619Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 136, 520, 138, 522, 140, 524, 142, 526, 201, 585, 203, 587, 205, 589, 207, 591, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967, 392, 776, 394, 778, 396, 780, 398, 782, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition2619Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2619Input0) = fromList transition2619Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2619 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0381 = 1 • support0438 := by
  have hs : support0381 = fromList transition2619Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2619Chunk0]
  have hn : (transition2619Raw0 : Multiset ℕ) = 1 • (supportNumbers0438 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0438] using hm

private def transition2620Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 512, 514, 516, 518, 577, 579, 581, 583, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2620Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private theorem transition2620Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2620Input0) = fromList transition2620Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2620 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0381 = 1 • support0437 := by
  have hs : support0381 = fromList transition2620Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2620Chunk0]
  have hn : (transition2620Raw0 : Multiset ℕ) = 1 • (supportNumbers0437 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0437] using hm

private def transition2621Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2621Raw0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205, 2, 6, 67, 71, 138, 142, 203, 207]
private theorem transition2621Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2621Input0) = fromList transition2621Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2621 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0437 = 1 • support0076 := by
  have hs : support0437 = fromList transition2621Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2621Chunk0]
  have hn : (transition2621Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition2622Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition2622Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 136, 714, 140, 718, 201, 651, 205, 655, 576, 2, 580, 6, 513, 67, 517, 71, 712, 138, 716, 142, 649, 203, 653, 207]
private theorem transition2622Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2622Input0) = fromList transition2622Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2622 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0437 = 1 • support0731 := by
  have hs : support0437 = fromList transition2622Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2622Chunk0]
  have hn : (transition2622Raw0 : Multiset ℕ) = 1 • (supportNumbers0731 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0731] using hm

private def transition2623Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 512, 514, 516, 518, 577, 579, 581, 583, 648, 650, 652, 654, 713, 715, 717, 719]
private def transition2623Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 392, 936, 394, 938, 396, 940, 398, 942, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition2623Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2623Input0) = fromList transition2623Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2623 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0381 = 1 • support1689 := by
  have hs : support0381 = fromList transition2623Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2623Chunk0]
  have hn : (transition2623Raw0 : Multiset ℕ) = 1 • (supportNumbers1689 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1689] using hm

private def transition2624Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 800, 802, 804, 806, 865, 867, 869, 871, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2624Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495, 288, 290, 292, 294, 353, 355, 357, 359, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition2624Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2624Input0) = fromList transition2624Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2624 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1689 = 2 • support0601 := by
  have hs : support1689 = fromList transition2624Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2624Chunk0]
  have hn : (transition2624Raw0 : Multiset ℕ) = 2 • (supportNumbers0601 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0601] using hm

private def transition2625Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 256, 258, 260, 262, 321, 323, 325, 327, 392, 394, 396, 398, 457, 459, 461, 463, 544, 546, 548, 550, 609, 611, 613, 615, 680, 682, 684, 686, 745, 747, 749, 751, 800, 802, 804, 806, 865, 867, 869, 871, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def transition2625Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition2625Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2625Input0) = fromList transition2625Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2625 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1689 = 2 • support0603 := by
  have hs : support1689 = fromList transition2625Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2625Chunk0]
  have hn : (transition2625Raw0 : Multiset ℕ) = 2 • (supportNumbers0603 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0603] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
