import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2573Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 572, 573, 574, 575, 680, 681, 682, 683]
private def transition2573Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition2573Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2573Input0) = fromList transition2573Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2573 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1682 = 1 • support1684 := by
  have hs : support1682 = fromList transition2573Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2573Chunk0]
  have hn : (transition2573Raw0 : Multiset ℕ) = 1 • (supportNumbers1684 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1684] using hm

private def transition2574Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2574Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private theorem transition2574Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2574Input0) = fromList transition2574Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2574 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0374 = 1 • support0374 := by
  have hs : support0374 = fromList transition2574Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2574Chunk0]
  have hn : (transition2574Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2575Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2575Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535]
private theorem transition2575Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2575Input0) = fromList transition2575Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2575 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0374 = 1 • support0432 := by
  have hs : support0374 = fromList transition2575Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2575Chunk0]
  have hn : (transition2575Raw0 : Multiset ℕ) = 1 • (supportNumbers0432 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0432] using hm

private def transition2576Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2576Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private theorem transition2576Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2576Input0) = fromList transition2576Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2576 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0374 = 1 • support0374 := by
  have hs : support0374 = fromList transition2576Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2576Chunk0]
  have hn : (transition2576Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2577Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2577Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695]
private theorem transition2577Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2577Input0) = fromList transition2577Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2577 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0374 = 1 • support1686 := by
  have hs : support0374 = fromList transition2577Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2577Chunk0]
  have hn : (transition2577Raw0 : Multiset ℕ) = 1 • (supportNumbers1686 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1686] using hm

private def transition2578Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695]
private def transition2578Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 288, 289, 290, 291, 316, 317, 318, 319, 424, 425, 426, 427, 436, 437, 438, 439]
private theorem transition2578Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2578Input0) = fromList transition2578Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2578 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1686 = 1 • support0579 := by
  have hs : support1686 = fromList transition2578Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2578Chunk0]
  have hn : (transition2578Raw0 : Multiset ℕ) = 1 • (supportNumbers0579 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0579] using hm

private def transition2579Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695]
private def transition2579Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition2579Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2579Input0) = fromList transition2579Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2579 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1686 = 1 • support0581 := by
  have hs : support1686 = fromList transition2579Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2579Chunk0]
  have hn : (transition2579Raw0 : Multiset ℕ) = 1 • (supportNumbers0581 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0581] using hm

private def transition2580Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 512, 513, 514, 515, 540, 541, 542, 543, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition2580Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition2580Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2580Input0) = fromList transition2580Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2580 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0375 = 1 • support0433 := by
  have hs : support0375 = fromList transition2580Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2580Chunk0]
  have hn : (transition2580Raw0 : Multiset ℕ) = 1 • (supportNumbers0433 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0433] using hm

private def transition2581Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 512, 513, 514, 515, 540, 541, 542, 543, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition2581Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition2581Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2581Input0) = fromList transition2581Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2581 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0375 = 1 • support0434 := by
  have hs : support0375 = fromList transition2581Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2581Chunk0]
  have hn : (transition2581Raw0 : Multiset ℕ) = 1 • (supportNumbers0434 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0434] using hm

private def transition2582Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 512, 513, 514, 515, 540, 541, 542, 543, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition2582Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private theorem transition2582Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2582Input0) = fromList transition2582Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2582 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0375 = 1 • support0433 := by
  have hs : support0375 = fromList transition2582Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2582Chunk0]
  have hn : (transition2582Raw0 : Multiset ℕ) = 1 • (supportNumbers0433 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0433] using hm

private def transition2583Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2583Raw0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149, 2, 3, 30, 31, 138, 139, 150, 151]
private theorem transition2583Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2583Input0) = fromList transition2583Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2583 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0433 = 1 • support0374 := by
  have hs : support0433 = fromList transition2583Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2583Chunk0]
  have hn : (transition2583Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2584Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407]
private def transition2584Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 136, 137, 714, 715, 148, 149, 726, 727, 576, 577, 2, 3, 604, 605, 30, 31, 712, 713, 138, 139, 724, 725, 150, 151]
private theorem transition2584Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2584Input0) = fromList transition2584Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2584 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0433 = 1 • support1543 := by
  have hs : support0433 = fromList transition2584Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2584Chunk0]
  have hn : (transition2584Raw0 : Multiset ℕ) = 1 • (supportNumbers1543 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1543] using hm

private def transition2585Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 512, 513, 514, 515, 540, 541, 542, 543, 648, 649, 650, 651, 660, 661, 662, 663]
private def transition2585Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition2585Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2585Input0) = fromList transition2585Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2585 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0375 = 1 • support1687 := by
  have hs : support0375 = fromList transition2585Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2585Chunk0]
  have hn : (transition2585Raw0 : Multiset ℕ) = 1 • (supportNumbers1687 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1687] using hm

private def transition2586Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695, 800, 801, 802, 803, 828, 829, 830, 831, 936, 937, 938, 939, 948, 949, 950, 951]
private def transition2586Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 288, 289, 290, 291, 316, 317, 318, 319, 424, 425, 426, 427, 436, 437, 438, 439, 288, 289, 290, 291, 316, 317, 318, 319, 424, 425, 426, 427, 436, 437, 438, 439]
private theorem transition2586Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2586Input0) = fromList transition2586Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2586 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1687 = 2 • support0579 := by
  have hs : support1687 = fromList transition2586Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2586Chunk0]
  have hn : (transition2586Raw0 : Multiset ℕ) = 2 • (supportNumbers0579 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0579] using hm

private def transition2587Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 256, 257, 258, 259, 284, 285, 286, 287, 392, 393, 394, 395, 404, 405, 406, 407, 544, 545, 546, 547, 572, 573, 574, 575, 680, 681, 682, 683, 692, 693, 694, 695, 800, 801, 802, 803, 828, 829, 830, 831, 936, 937, 938, 939, 948, 949, 950, 951]
private def transition2587Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition2587Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2587Input0) = fromList transition2587Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2587 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1687 = 2 • support0581 := by
  have hs : support1687 = fromList transition2587Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2587Chunk0]
  have hn : (transition2587Raw0 : Multiset ℕ) = 2 • (supportNumbers0581 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0581] using hm

private def transition2588Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 512, 513, 514, 515, 532, 533, 534, 535]
private def transition2588Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private theorem transition2588Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2588Input0) = fromList transition2588Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2588 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0376 = 1 • support0435 := by
  have hs : support0376 = fromList transition2588Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2588Chunk0]
  have hn : (transition2588Raw0 : Multiset ℕ) = 1 • (supportNumbers0435 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0435] using hm

private def transition2589Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 512, 513, 514, 515, 532, 533, 534, 535]
private def transition2589Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919]
private theorem transition2589Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2589Input0) = fromList transition2589Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2589 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0376 = 1 • support0436 := by
  have hs : support0376 = fromList transition2589Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2589Chunk0]
  have hn : (transition2589Raw0 : Multiset ℕ) = 1 • (supportNumbers0436 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0436] using hm

private def transition2590Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 512, 513, 514, 515, 532, 533, 534, 535]
private def transition2590Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private theorem transition2590Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2590Input0) = fromList transition2590Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2590 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0376 = 1 • support0435 := by
  have hs : support0376 = fromList transition2590Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2590Chunk0]
  have hn : (transition2590Raw0 : Multiset ℕ) = 1 • (supportNumbers0435 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0435] using hm

private def transition2591Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2591Raw0 : List ℕ := [0, 1, 20, 21, 2, 3, 22, 23]
private theorem transition2591Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2591Input0) = fromList transition2591Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2591 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0435 = 1 • support0069 := by
  have hs : support0435 = fromList transition2591Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2591Chunk0]
  have hn : (transition2591Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition2592Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279]
private def transition2592Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 576, 577, 2, 3, 596, 597, 22, 23]
private theorem transition2592Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2592Input0) = fromList transition2592Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2592 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0435 = 1 • support0882 := by
  have hs : support0435 = fromList transition2592Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2592Chunk0]
  have hn : (transition2592Raw0 : Multiset ℕ) = 1 • (supportNumbers0882 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0882] using hm

private def transition2593Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 512, 513, 514, 515, 532, 533, 534, 535]
private def transition2593Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823]
private theorem transition2593Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2593Input0) = fromList transition2593Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2593 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0376 = 1 • support1688 := by
  have hs : support0376 = fromList transition2593Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2593Chunk0]
  have hn : (transition2593Raw0 : Multiset ℕ) = 1 • (supportNumbers1688 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1688] using hm

private def transition2594Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 544, 545, 546, 547, 564, 565, 566, 567, 800, 801, 802, 803, 820, 821, 822, 823]
private def transition2594Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 0, 1, 2, 3, 20, 21, 22, 23, 288, 289, 290, 291, 308, 309, 310, 311, 288, 289, 290, 291, 308, 309, 310, 311]
private theorem transition2594Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2594Input0) = fromList transition2594Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2594 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1688 = 2 • support1121 := by
  have hs : support1688 = fromList transition2594Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2594Chunk0]
  have hn : (transition2594Raw0 : Multiset ℕ) = 2 • (supportNumbers1121 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1121] using hm

private def transition2595Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 256, 257, 258, 259, 276, 277, 278, 279, 544, 545, 546, 547, 564, 565, 566, 567, 800, 801, 802, 803, 820, 821, 822, 823]
private def transition2595Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887]
private theorem transition2595Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2595Input0) = fromList transition2595Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2595 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1688 = 2 • support1122 := by
  have hs : support1688 = fromList transition2595Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2595Chunk0]
  have hn : (transition2595Raw0 : Multiset ℕ) = 2 • (supportNumbers1122 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1122] using hm

private def transition2596Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2596Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition2596Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2596Input0) = fromList transition2596Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2596 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0377 = 1 • support0130 := by
  have hs : support0377 = fromList transition2596Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2596Chunk0]
  have hn : (transition2596Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition2597Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2597Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 640, 641, 642, 643, 660, 661, 662, 663, 512, 513, 514, 515, 532, 533, 534, 535]
private theorem transition2597Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2597Input0) = fromList transition2597Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2597 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0377 = 1 • support0296 := by
  have hs : support0377 = fromList transition2597Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2597Chunk0]
  have hn : (transition2597Raw0 : Multiset ℕ) = 1 • (supportNumbers0296 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0296] using hm

private def transition2598Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2598Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition2598Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2598Input0) = fromList transition2598Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2598 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0377 = 1 • support0130 := by
  have hs : support0377 = fromList transition2598Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2598Chunk0]
  have hn : (transition2598Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition2599Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition2599Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695]
private theorem transition2599Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2599Input0) = fromList transition2599Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2599 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0377 = 1 • support1370 := by
  have hs : support0377 = fromList transition2599Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2599Chunk0]
  have hn : (transition2599Raw0 : Multiset ℕ) = 1 • (supportNumbers1370 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1370] using hm

private def transition2600Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 768, 769, 770, 771, 788, 789, 790, 791, 896, 897, 898, 899, 916, 917, 918, 919]
private def transition2600Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2600Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2600Input0) = fromList transition2600Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2600 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0378 = 2 • support0377 := by
  have hs : support0378 = fromList transition2600Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2600Chunk0]
  have hn : (transition2600Raw0 : Multiset ℕ) = 2 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
