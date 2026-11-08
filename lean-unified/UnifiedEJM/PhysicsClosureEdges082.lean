import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1473Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703, 820, 821, 822, 823, 828, 829, 830, 831, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition1473Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition1473Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1473Input0) = fromList transition1473Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1473 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1355 = 1 • support0508 := by
  have hs : support1355 = fromList transition1473Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1473Chunk0]
  have hn : (transition1473Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition1474Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition1474Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition1474Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1474Input0) = fromList transition1474Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1474 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0203 = 1 • support0290 := by
  have hs : support0203 = fromList transition1474Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1474Chunk0]
  have hn : (transition1474Raw0 : Multiset ℕ) = 1 • (supportNumbers0290 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0290] using hm

private def transition1475Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition1475Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition1475Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1475Input0) = fromList transition1475Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1475 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0203 = 1 • support0291 := by
  have hs : support0203 = fromList transition1475Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1475Chunk0]
  have hn : (transition1475Raw0 : Multiset ℕ) = 1 • (supportNumbers0291 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0291] using hm

private def transition1476Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition1476Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition1476Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1476Input0) = fromList transition1476Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1476 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0203 = 1 • support0290 := by
  have hs : support0203 = fromList transition1476Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1476Chunk0]
  have hn : (transition1476Raw0 : Multiset ℕ) = 1 • (supportNumbers0290 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0290] using hm

private def transition1477Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition1477Raw0 : List ℕ := [0, 1, 20, 21, 130, 131, 150, 151]
private theorem transition1477Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1477Input0) = fromList transition1477Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1477 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0290 = 1 • support1356 := by
  have hs : support0290 = fromList transition1477Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1477Chunk0]
  have hn : (transition1477Raw0 : Multiset ℕ) = 1 • (supportNumbers1356 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1356] using hm

private def transition1478Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407]
private def transition1478Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 704, 705, 130, 131, 724, 725, 150, 151]
private theorem transition1478Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1478Input0) = fromList transition1478Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1478 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0290 = 1 • support1357 := by
  have hs : support0290 = fromList transition1478Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1478Chunk0]
  have hn : (transition1478Raw0 : Multiset ℕ) = 1 • (supportNumbers1357 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1357] using hm

private def transition1479Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition1479Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition1479Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1479Input0) = fromList transition1479Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1479 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0203 = 1 • support1359 := by
  have hs : support0203 = fromList transition1479Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1479Chunk0]
  have hn : (transition1479Raw0 : Multiset ℕ) = 1 • (supportNumbers1359 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1359] using hm

private def transition1480Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition1480Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition1480Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1480Input0) = fromList transition1480Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1480 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1359 = 1 • support1360 := by
  have hs : support1359 = fromList transition1480Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1480Chunk0]
  have hn : (transition1480Raw0 : Multiset ℕ) = 1 • (supportNumbers1360 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1360] using hm

private def transition1481Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 384, 385, 386, 387, 404, 405, 406, 407, 544, 545, 546, 547, 564, 565, 566, 567, 928, 929, 930, 931, 948, 949, 950, 951]
private def transition1481Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition1481Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1481Input0) = fromList transition1481Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1481 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1359 = 1 • support1362 := by
  have hs : support1359 = fromList transition1481Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1481Chunk0]
  have hn : (transition1481Raw0 : Multiset ℕ) = 1 • (supportNumbers1362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1362] using hm

private def transition1482Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1482Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition1482Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1482Input0) = fromList transition1482Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1482 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0204 = 1 • support0069 := by
  have hs : support0204 = fromList transition1482Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1482Chunk0]
  have hn : (transition1482Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition1483Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1483Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 20, 21, 22, 23, 668, 669, 670, 671]
private theorem transition1483Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1483Input0) = fromList transition1483Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1483 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0204 = 1 • support0292 := by
  have hs : support0204 = fromList transition1483Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1483Chunk0]
  have hn : (transition1483Raw0 : Multiset ℕ) = 1 • (supportNumbers0292 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0292] using hm

private def transition1484Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1484Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23]
private theorem transition1484Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1484Input0) = fromList transition1484Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1484 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0204 = 1 • support0069 := by
  have hs : support0204 = fromList transition1484Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1484Chunk0]
  have hn : (transition1484Raw0 : Multiset ℕ) = 1 • (supportNumbers0069 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0069] using hm

private def transition1485Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1485Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 20, 21, 22, 23, 572, 573, 574, 575]
private theorem transition1485Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1485Input0) = fromList transition1485Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1485 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0204 = 1 • support1364 := by
  have hs : support0204 = fromList transition1485Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1485Chunk0]
  have hn : (transition1485Raw0 : Multiset ℕ) = 1 • (supportNumbers1364 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1364] using hm

private def transition1486Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 552, 553, 554, 555, 572, 573, 574, 575]
private def transition1486Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 296, 297, 298, 299, 316, 317, 318, 319]
private theorem transition1486Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1486Input0) = fromList transition1486Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1486 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1364 = 1 • support1365 := by
  have hs : support1364 = fromList transition1486Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1486Chunk0]
  have hn : (transition1486Raw0 : Multiset ℕ) = 1 • (supportNumbers1365 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1365] using hm

private def transition1487Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 552, 553, 554, 555, 572, 573, 574, 575]
private def transition1487Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1487Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1487Input0) = fromList transition1487Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1487 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1364 = 1 • support1366 := by
  have hs : support1364 = fromList transition1487Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1487Chunk0]
  have hn : (transition1487Raw0 : Multiset ℕ) = 1 • (supportNumbers1366 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1366] using hm

private def transition1488Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1488Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private theorem transition1488Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1488Input0) = fromList transition1488Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1488 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0204 = 1 • support0204 := by
  have hs : support0204 = fromList transition1488Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1488Chunk0]
  have hn : (transition1488Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition1489Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1489Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671]
private theorem transition1489Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1489Input0) = fromList transition1489Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1489 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0204 = 1 • support0293 := by
  have hs : support0204 = fromList transition1489Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1489Chunk0]
  have hn : (transition1489Raw0 : Multiset ℕ) = 1 • (supportNumbers0293 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0293] using hm

private def transition1490Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1490Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private theorem transition1490Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1490Input0) = fromList transition1490Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1490 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0204 = 1 • support0204 := by
  have hs : support0204 = fromList transition1490Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1490Chunk0]
  have hn : (transition1490Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition1491Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31]
private def transition1491Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575]
private theorem transition1491Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1491Input0) = fromList transition1491Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1491 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0204 = 1 • support1368 := by
  have hs : support0204 = fromList transition1491Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1491Chunk0]
  have hn : (transition1491Raw0 : Multiset ℕ) = 1 • (supportNumbers1368 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1368] using hm

private def transition1492Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575]
private def transition1492Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319]
private theorem transition1492Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1492Input0) = fromList transition1492Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1492 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1368 = 1 • support0889 := by
  have hs : support1368 = fromList transition1492Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1492Chunk0]
  have hn : (transition1492Raw0 : Multiset ℕ) = 1 • (supportNumbers0889 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0889] using hm

private def transition1493Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575]
private def transition1493Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1493Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1493Input0) = fromList transition1493Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1493 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1368 = 1 • support0890 := by
  have hs : support1368 = fromList transition1493Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1493Chunk0]
  have hn : (transition1493Raw0 : Multiset ℕ) = 1 • (supportNumbers0890 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0890] using hm

private def transition1494Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition1494Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition1494Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1494Input0) = fromList transition1494Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1494 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0205 = 1 • support0294 := by
  have hs : support0205 = fromList transition1494Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1494Chunk0]
  have hn : (transition1494Raw0 : Multiset ℕ) = 1 • (supportNumbers0294 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0294] using hm

private def transition1495Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition1495Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition1495Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1495Input0) = fromList transition1495Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1495 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0205 = 1 • support0295 := by
  have hs : support0205 = fromList transition1495Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1495Chunk0]
  have hn : (transition1495Raw0 : Multiset ℕ) = 1 • (supportNumbers0295 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0295] using hm

private def transition1496Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition1496Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private theorem transition1496Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1496Input0) = fromList transition1496Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1496 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0205 = 1 • support0294 := by
  have hs : support0205 = fromList transition1496Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1496Chunk0]
  have hn : (transition1496Raw0 : Multiset ℕ) = 1 • (supportNumbers0294 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0294] using hm

private def transition1497Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition1497Raw0 : List ℕ := [0, 1, 8, 9, 20, 21, 28, 29, 2, 3, 10, 11, 22, 23, 30, 31]
private theorem transition1497Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1497Input0) = fromList transition1497Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1497 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0294 = 1 • support0204 := by
  have hs : support0294 = fromList transition1497Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1497Chunk0]
  have hn : (transition1497Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition1498Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition1498Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 20, 21, 598, 599, 28, 29, 606, 607, 576, 577, 2, 3, 584, 585, 10, 11, 596, 597, 22, 23, 604, 605, 30, 31]
private theorem transition1498Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1498Input0) = fromList transition1498Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1498 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0294 = 1 • support1127 := by
  have hs : support0294 = fromList transition1498Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1498Chunk0]
  have hn : (transition1498Raw0 : Multiset ℕ) = 1 • (supportNumbers1127 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1127] using hm

private def transition1499Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543]
private def transition1499Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831]
private theorem transition1499Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1499Input0) = fromList transition1499Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1499 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0205 = 1 • support1369 := by
  have hs : support0205 = fromList transition1499Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1499Chunk0]
  have hn : (transition1499Raw0 : Multiset ℕ) = 1 • (supportNumbers1369 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1369] using hm

private def transition1500Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 800, 801, 802, 803, 808, 809, 810, 811, 820, 821, 822, 823, 828, 829, 830, 831]
private def transition1500Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319, 288, 289, 290, 291, 296, 297, 298, 299, 308, 309, 310, 311, 316, 317, 318, 319]
private theorem transition1500Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1500Input0) = fromList transition1500Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1500 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1369 = 2 • support0889 := by
  have hs : support1369 = fromList transition1500Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1500Chunk0]
  have hn : (transition1500Raw0 : Multiset ℕ) = 2 • (supportNumbers0889 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0889] using hm

private def transition1501Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 800, 801, 802, 803, 808, 809, 810, 811, 820, 821, 822, 823, 828, 829, 830, 831]
private def transition1501Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1501Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1501Input0) = fromList transition1501Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1501 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1369 = 2 • support0890 := by
  have hs : support1369 = fromList transition1501Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1501Chunk0]
  have hn : (transition1501Raw0 : Multiset ℕ) = 2 • (supportNumbers0890 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0890] using hm

private def transition1502Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition1502Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition1502Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1502Input0) = fromList transition1502Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1502 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition1502Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1502Chunk0]
  have hn : (transition1502Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition1503Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition1503Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535]
private theorem transition1503Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1503Input0) = fromList transition1503Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1503 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0130 = 1 • support0296 := by
  have hs : support0130 = fromList transition1503Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1503Chunk0]
  have hn : (transition1503Raw0 : Multiset ℕ) = 1 • (supportNumbers0296 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0296] using hm

private def transition1504Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition1504Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private theorem transition1504Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1504Input0) = fromList transition1504Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1504 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0130 = 1 • support0130 := by
  have hs : support0130 = fromList transition1504Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1504Chunk0]
  have hn : (transition1504Raw0 : Multiset ℕ) = 1 • (supportNumbers0130 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0130] using hm

private def transition1505Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151]
private def transition1505Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695]
private theorem transition1505Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1505Input0) = fromList transition1505Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1505 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0130 = 1 • support1370 := by
  have hs : support0130 = fromList transition1505Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1505Chunk0]
  have hn : (transition1505Raw0 : Multiset ℕ) = 1 • (supportNumbers1370 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1370] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
