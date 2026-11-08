import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2530Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799]
private def transition2530Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287]
private theorem transition2530Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2530Input0) = fromList transition2530Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2530 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0368 = 1 • support0194 := by
  have hs : support0368 = fromList transition2530Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2530Chunk0]
  have hn : (transition2530Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2531Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799]
private def transition2531Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 156, 700, 157, 701, 158, 702, 159, 703, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition2531Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2531Input0) = fromList transition2531Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2531 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0368 = 1 • support1095 := by
  have hs : support0368 = fromList transition2531Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2531Chunk0]
  have hn : (transition2531Raw0 : Multiset ℕ) = 1 • (supportNumbers1095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1095] using hm

private def transition2532Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2532Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2532Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2532Input0) = fromList transition2532Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2532 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0369 = 1 • support0367 := by
  have hs : support0369 = fromList transition2532Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2532Chunk0]
  have hn : (transition2532Raw0 : Multiset ℕ) = 1 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition2533Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2533Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2533Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2533Input0) = fromList transition2533Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2533 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0369 = 1 • support0368 := by
  have hs : support0369 = fromList transition2533Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2533Chunk0]
  have hn : (transition2533Raw0 : Multiset ℕ) = 1 • (supportNumbers0368 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0368] using hm

private def transition2534Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2534Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2534Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2534Input0) = fromList transition2534Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2534 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0369 = 1 • support0367 := by
  have hs : support0369 = fromList transition2534Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2534Chunk0]
  have hn : (transition2534Raw0 : Multiset ℕ) = 1 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition2535Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2535Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2535Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2535Input0) = fromList transition2535Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2535 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0369 = 1 • support1521 := by
  have hs : support0369 = fromList transition2535Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2535Chunk0]
  have hn : (transition2535Raw0 : Multiset ℕ) = 1 • (supportNumbers1521 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1521] using hm

private def transition2536Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 540, 541, 542, 543, 668, 669, 670, 671]
private def transition2536Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private theorem transition2536Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2536Input0) = fromList transition2536Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2536 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0370 = 1 • support0425 := by
  have hs : support0370 = fromList transition2536Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2536Chunk0]
  have hn : (transition2536Raw0 : Multiset ℕ) = 1 • (supportNumbers0425 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0425] using hm

private def transition2537Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 540, 541, 542, 543, 668, 669, 670, 671]
private def transition2537Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 284, 924, 285, 925, 286, 926, 287, 927, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2537Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2537Input0) = fromList transition2537Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2537 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0370 = 1 • support0426 := by
  have hs : support0370 = fromList transition2537Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2537Chunk0]
  have hn : (transition2537Raw0 : Multiset ℕ) = 1 • (supportNumbers0426 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0426] using hm

private def transition2538Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 540, 541, 542, 543, 668, 669, 670, 671]
private def transition2538Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private theorem transition2538Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2538Input0) = fromList transition2538Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2538 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0370 = 1 • support0425 := by
  have hs : support0370 = fromList transition2538Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2538Chunk0]
  have hn : (transition2538Raw0 : Multiset ℕ) = 1 • (supportNumbers0425 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0425] using hm

private def transition2539Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2539Raw0 : List ℕ := [0, 1, 128, 129, 30, 31, 158, 159]
private theorem transition2539Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2539Input0) = fromList transition2539Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2539 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0425 = 1 • support1669 := by
  have hs : support0425 = fromList transition2539Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2539Chunk0]
  have hn : (transition2539Raw0 : Multiset ℕ) = 1 • (supportNumbers1669 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1669] using hm

private def transition2540Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415]
private def transition2540Raw0 : List ℕ := [0, 1, 578, 579, 128, 129, 706, 707, 604, 605, 30, 31, 732, 733, 158, 159]
private theorem transition2540Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2540Input0) = fromList transition2540Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2540 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0425 = 1 • support1670 := by
  have hs : support0425 = fromList transition2540Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2540Chunk0]
  have hn : (transition2540Raw0 : Multiset ℕ) = 1 • (supportNumbers1670 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1670] using hm

private def transition2541Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 540, 541, 542, 543, 668, 669, 670, 671]
private def transition2541Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 284, 828, 285, 829, 286, 830, 287, 831, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2541Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2541Input0) = fromList transition2541Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2541 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0370 = 1 • support1672 := by
  have hs : support0370 = fromList transition2541Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2541Chunk0]
  have hn : (transition2541Raw0 : Multiset ℕ) = 1 • (supportNumbers1672 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1672] using hm

private def transition2542Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 544, 545, 546, 547, 672, 673, 674, 675, 828, 829, 830, 831, 956, 957, 958, 959]
private def transition2542Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 28, 29, 30, 31, 156, 157, 158, 159, 288, 289, 290, 291, 416, 417, 418, 419, 316, 317, 318, 319, 444, 445, 446, 447]
private theorem transition2542Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2542Input0) = fromList transition2542Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2542 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1672 = 1 • support0861 := by
  have hs : support1672 = fromList transition2542Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2542Chunk0]
  have hn : (transition2542Raw0 : Multiset ℕ) = 1 • (supportNumbers0861 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0861] using hm

private def transition2543Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 284, 285, 286, 287, 412, 413, 414, 415, 544, 545, 546, 547, 672, 673, 674, 675, 828, 829, 830, 831, 956, 957, 958, 959]
private def transition2543Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 28, 604, 29, 605, 30, 606, 31, 607, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995, 316, 892, 317, 893, 318, 894, 319, 895, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2543Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2543Input0) = fromList transition2543Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2543 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1672 = 1 • support0863 := by
  have hs : support1672 = fromList transition2543Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2543Chunk0]
  have hn : (transition2543Raw0 : Multiset ℕ) = 1 • (supportNumbers0863 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0863] using hm

private def transition2544Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 512, 513, 514, 515, 648, 649, 650, 651]
private def transition2544Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private theorem transition2544Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2544Input0) = fromList transition2544Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2544 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0371 = 1 • support0427 := by
  have hs : support0371 = fromList transition2544Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2544Chunk0]
  have hn : (transition2544Raw0 : Multiset ℕ) = 1 • (supportNumbers0427 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0427] using hm

private def transition2545Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 512, 513, 514, 515, 648, 649, 650, 651]
private def transition2545Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 256, 896, 257, 897, 258, 898, 259, 899, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition2545Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2545Input0) = fromList transition2545Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2545 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0371 = 1 • support0428 := by
  have hs : support0371 = fromList transition2545Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2545Chunk0]
  have hn : (transition2545Raw0 : Multiset ℕ) = 1 • (supportNumbers0428 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0428] using hm

private def transition2546Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 512, 513, 514, 515, 648, 649, 650, 651]
private def transition2546Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private theorem transition2546Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2546Input0) = fromList transition2546Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2546 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0371 = 1 • support0427 := by
  have hs : support0371 = fromList transition2546Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2546Chunk0]
  have hn : (transition2546Raw0 : Multiset ℕ) = 1 • (supportNumbers0427 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0427] using hm

private def transition2547Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2547Raw0 : List ℕ := [0, 1, 136, 137, 2, 3, 138, 139]
private theorem transition2547Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2547Input0) = fromList transition2547Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2547 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0427 = 1 • support0065 := by
  have hs : support0427 = fromList transition2547Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2547Chunk0]
  have hn : (transition2547Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2548Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395]
private def transition2548Raw0 : List ℕ := [0, 1, 578, 579, 136, 137, 714, 715, 576, 577, 2, 3, 712, 713, 138, 139]
private theorem transition2548Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2548Input0) = fromList transition2548Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2548 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0427 = 1 • support1654 := by
  have hs : support0427 = fromList transition2548Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2548Chunk0]
  have hn : (transition2548Raw0 : Multiset ℕ) = 1 • (supportNumbers1654 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1654] using hm

private def transition2549Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 512, 513, 514, 515, 648, 649, 650, 651]
private def transition2549Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 256, 800, 257, 801, 258, 802, 259, 803, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition2549Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2549Input0) = fromList transition2549Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2549 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0371 = 1 • support1673 := by
  have hs : support0371 = fromList transition2549Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2549Chunk0]
  have hn : (transition2549Raw0 : Multiset ℕ) = 1 • (supportNumbers1673 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1673] using hm

private def transition2550Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 544, 545, 546, 547, 680, 681, 682, 683, 800, 801, 802, 803, 936, 937, 938, 939]
private def transition2550Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 0, 1, 2, 3, 136, 137, 138, 139, 288, 289, 290, 291, 424, 425, 426, 427, 288, 289, 290, 291, 424, 425, 426, 427]
private theorem transition2550Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2550Input0) = fromList transition2550Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2550 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1673 = 2 • support0668 := by
  have hs : support1673 = fromList transition2550Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2550Chunk0]
  have hn : (transition2550Raw0 : Multiset ℕ) = 2 • (supportNumbers0668 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0668] using hm

private def transition2551Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 256, 257, 258, 259, 392, 393, 394, 395, 544, 545, 546, 547, 680, 681, 682, 683, 800, 801, 802, 803, 936, 937, 938, 939]
private def transition2551Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition2551Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2551Input0) = fromList transition2551Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2551 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1673 = 2 • support0669 := by
  have hs : support1673 = fromList transition2551Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2551Chunk0]
  have hn : (transition2551Raw0 : Multiset ℕ) = 2 • (supportNumbers0669 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0669] using hm

private def transition2552Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition2552Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition2552Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2552Input0) = fromList transition2552Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2552 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0372 = 1 • support0002 := by
  have hs : support0372 = fromList transition2552Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2552Chunk0]
  have hn : (transition2552Raw0 : Multiset ℕ) = 1 • (supportNumbers0002 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0002] using hm

private def transition2553Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition2553Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition2553Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2553Input0) = fromList transition2553Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2553 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0372 = 1 • support0003 := by
  have hs : support0372 = fromList transition2553Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2553Chunk0]
  have hn : (transition2553Raw0 : Multiset ℕ) = 1 • (supportNumbers0003 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0003] using hm

private def transition2554Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition2554Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition2554Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2554Input0) = fromList transition2554Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2554 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0372 = 1 • support0002 := by
  have hs : support0372 = fromList transition2554Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2554Chunk0]
  have hn : (transition2554Raw0 : Multiset ℕ) = 1 • (supportNumbers0002 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0002] using hm

private def transition2555Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2555Raw0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31]
private theorem transition2555Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2555Input0) = fromList transition2555Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2555 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0002 = 1 • support1674 := by
  have hs : support0002 = fromList transition2555Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2555Chunk0]
  have hn : (transition2555Raw0 : Multiset ℕ) = 1 • (supportNumbers1674 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1674] using hm

private def transition2556Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2556Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 596, 597, 22, 23, 604, 605, 30, 31]
private theorem transition2556Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2556Input0) = fromList transition2556Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2556 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0002 = 1 • support1675 := by
  have hs : support0002 = fromList transition2556Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2556Chunk0]
  have hn : (transition2556Raw0 : Multiset ℕ) = 1 • (supportNumbers1675 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1675] using hm

private def transition2557Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition2557Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition2557Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2557Input0) = fromList transition2557Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2557 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0372 = 1 • support1677 := by
  have hs : support0372 = fromList transition2557Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2557Chunk0]
  have hn : (transition2557Raw0 : Multiset ℕ) = 1 • (supportNumbers1677 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1677] using hm

private def transition2558Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 544, 545, 546, 547, 552, 553, 554, 555, 820, 821, 822, 823, 828, 829, 830, 831]
private def transition2558Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319]
private theorem transition2558Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2558Input0) = fromList transition2558Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2558 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1677 = 1 • support0889 := by
  have hs : support1677 = fromList transition2558Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2558Chunk0]
  have hn : (transition2558Raw0 : Multiset ℕ) = 1 • (supportNumbers0889 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0889] using hm

private def transition2559Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 276, 277, 278, 279, 284, 285, 286, 287, 544, 545, 546, 547, 552, 553, 554, 555, 820, 821, 822, 823, 828, 829, 830, 831]
private def transition2559Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition2559Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2559Input0) = fromList transition2559Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2559 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1677 = 1 • support0890 := by
  have hs : support1677 = fromList transition2559Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2559Chunk0]
  have hn : (transition2559Raw0 : Multiset ℕ) = 1 • (supportNumbers0890 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0890] using hm

private def transition2560Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 532, 533, 534, 535, 640, 641, 642, 643]
private def transition2560Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private theorem transition2560Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2560Input0) = fromList transition2560Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2560 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0373 = 1 • support0429 := by
  have hs : support0373 = fromList transition2560Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2560Chunk0]
  have hn : (transition2560Raw0 : Multiset ℕ) = 1 • (supportNumbers0429 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0429] using hm

private def transition2561Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 532, 533, 534, 535, 640, 641, 642, 643]
private def transition2561Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition2561Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2561Input0) = fromList transition2561Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2561 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0373 = 1 • support0430 := by
  have hs : support0373 = fromList transition2561Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2561Chunk0]
  have hn : (transition2561Raw0 : Multiset ℕ) = 1 • (supportNumbers0430 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0430] using hm

private def transition2562Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 532, 533, 534, 535, 640, 641, 642, 643]
private def transition2562Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private theorem transition2562Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2562Input0) = fromList transition2562Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2562 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0373 = 1 • support0429 := by
  have hs : support0373 = fromList transition2562Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2562Chunk0]
  have hn : (transition2562Raw0 : Multiset ℕ) = 1 • (supportNumbers0429 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0429] using hm

private def transition2563Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2563Raw0 : List ℕ := [0, 1, 148, 149, 22, 23, 130, 131]
private theorem transition2563Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2563Input0) = fromList transition2563Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2563 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0429 = 1 • support1678 := by
  have hs : support0429 = fromList transition2563Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2563Chunk0]
  have hn : (transition2563Raw0 : Multiset ℕ) = 1 • (supportNumbers1678 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1678] using hm

private def transition2564Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387]
private def transition2564Raw0 : List ℕ := [0, 1, 578, 579, 148, 149, 726, 727, 596, 597, 22, 23, 704, 705, 130, 131]
private theorem transition2564Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2564Input0) = fromList transition2564Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2564 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0429 = 1 • support1679 := by
  have hs : support0429 = fromList transition2564Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2564Chunk0]
  have hn : (transition2564Raw0 : Multiset ℕ) = 1 • (supportNumbers1679 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1679] using hm

private def transition2565Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 532, 533, 534, 535, 640, 641, 642, 643]
private def transition2565Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition2565Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2565Input0) = fromList transition2565Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2565 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0373 = 1 • support1681 := by
  have hs : support0373 = fromList transition2565Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2565Chunk0]
  have hn : (transition2565Raw0 : Multiset ℕ) = 1 • (supportNumbers1681 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1681] using hm

private def transition2566Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 544, 545, 546, 547, 692, 693, 694, 695, 820, 821, 822, 823, 928, 929, 930, 931]
private def transition2566Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 20, 21, 22, 23, 128, 129, 130, 131, 288, 289, 290, 291, 436, 437, 438, 439, 308, 309, 310, 311, 416, 417, 418, 419]
private theorem transition2566Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2566Input0) = fromList transition2566Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2566 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1681 = 1 • support1360 := by
  have hs : support1681 = fromList transition2566Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2566Chunk0]
  have hn : (transition2566Raw0 : Multiset ℕ) = 1 • (supportNumbers1360 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1360] using hm

private def transition2567Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 276, 277, 278, 279, 384, 385, 386, 387, 544, 545, 546, 547, 692, 693, 694, 695, 820, 821, 822, 823, 928, 929, 930, 931]
private def transition2567Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition2567Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2567Input0) = fromList transition2567Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2567 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1681 = 1 • support1362 := by
  have hs : support1681 = fromList transition2567Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2567Chunk0]
  have hn : (transition2567Raw0 : Multiset ℕ) = 1 • (supportNumbers1362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1362] using hm

private def transition2568Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2568Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2568Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2568Input0) = fromList transition2568Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2568 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0374 = 1 • support0199 := by
  have hs : support0374 = fromList transition2568Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2568Chunk0]
  have hn : (transition2568Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2569Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2569Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 520, 521, 522, 523, 148, 149, 150, 151]
private theorem transition2569Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2569Input0) = fromList transition2569Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2569 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0374 = 1 • support0431 := by
  have hs : support0374 = fromList transition2569Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2569Chunk0]
  have hn : (transition2569Raw0 : Multiset ℕ) = 1 • (supportNumbers0431 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0431] using hm

private def transition2570Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2570Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2570Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2570Input0) = fromList transition2570Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2570 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0374 = 1 • support0199 := by
  have hs : support0374 = fromList transition2570Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2570Chunk0]
  have hn : (transition2570Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2571Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2571Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 680, 681, 682, 683, 148, 149, 150, 151]
private theorem transition2571Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2571Input0) = fromList transition2571Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2571 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0374 = 1 • support1682 := by
  have hs : support0374 = fromList transition2571Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2571Chunk0]
  have hn : (transition2571Raw0 : Multiset ℕ) = 1 • (supportNumbers1682 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1682] using hm

private def transition2572Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 572, 573, 574, 575, 680, 681, 682, 683]
private def transition2572Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 316, 317, 318, 319, 424, 425, 426, 427]
private theorem transition2572Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2572Input0) = fromList transition2572Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2572 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1682 = 1 • support1683 := by
  have hs : support1682 = fromList transition2572Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2572Chunk0]
  have hn : (transition2572Raw0 : Multiset ℕ) = 1 • (supportNumbers1683 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1683] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
