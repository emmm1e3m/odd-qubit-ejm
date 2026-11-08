import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1443Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 520, 521, 522, 523, 660, 661, 662, 663]
private def transition1443Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 264, 808, 265, 809, 266, 810, 267, 811, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition1443Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1443Input0) = fromList transition1443Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1443 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0198 = 1 • support1344 := by
  have hs : support0198 = fromList transition1443Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1443Chunk0]
  have hn : (transition1443Raw0 : Multiset ℕ) = 1 • (supportNumbers1344 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1344] using hm

private def transition1444Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 544, 545, 546, 547, 700, 701, 702, 703, 808, 809, 810, 811, 948, 949, 950, 951]
private def transition1444Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 8, 9, 10, 11, 148, 149, 150, 151, 288, 289, 290, 291, 444, 445, 446, 447, 296, 297, 298, 299, 436, 437, 438, 439]
private theorem transition1444Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1444Input0) = fromList transition1444Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1444 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1344 = 1 • support1116 := by
  have hs : support1344 = fromList transition1444Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1444Chunk0]
  have hn : (transition1444Raw0 : Multiset ℕ) = 1 • (supportNumbers1116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1116] using hm

private def transition1445Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 544, 545, 546, 547, 700, 701, 702, 703, 808, 809, 810, 811, 948, 949, 950, 951]
private def transition1445Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 296, 872, 297, 873, 298, 874, 299, 875, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition1445Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1445Input0) = fromList transition1445Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1445 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1344 = 1 • support1118 := by
  have hs : support1344 = fromList transition1445Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1445Chunk0]
  have hn : (transition1445Raw0 : Multiset ℕ) = 1 • (supportNumbers1118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1118] using hm

private def transition1446Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1446Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition1446Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1446Input0) = fromList transition1446Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1446 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition1446Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1446Chunk0]
  have hn : (transition1446Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition1447Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1447Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition1447Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1447Input0) = fromList transition1447Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1447 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition1447Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1447Chunk0]
  have hn : (transition1447Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition1448Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1448Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition1448Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1448Input0) = fromList transition1448Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1448 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition1448Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1448Chunk0]
  have hn : (transition1448Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition1449Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1449Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition1449Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1449Input0) = fromList transition1449Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1449 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition1449Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1449Chunk0]
  have hn : (transition1449Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition1450Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1450Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition1450Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1450Input0) = fromList transition1450Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1450 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition1450Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1450Chunk0]
  have hn : (transition1450Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition1451Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition1451Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727]
private theorem transition1451Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1451Input0) = fromList transition1451Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1451 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0199 = 1 • support1345 := by
  have hs : support0199 = fromList transition1451Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1451Chunk0]
  have hn : (transition1451Raw0 : Multiset ℕ) = 1 • (supportNumbers1345 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1345] using hm

private def transition1452Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 540, 541, 542, 543, 648, 649, 650, 651]
private def transition1452Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private theorem transition1452Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1452Input0) = fromList transition1452Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1452 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0200 = 1 • support0285 := by
  have hs : support0200 = fromList transition1452Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1452Chunk0]
  have hn : (transition1452Raw0 : Multiset ℕ) = 1 • (supportNumbers0285 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0285] using hm

private def transition1453Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 540, 541, 542, 543, 648, 649, 650, 651]
private def transition1453Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1453Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1453Input0) = fromList transition1453Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1453 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0200 = 1 • support0286 := by
  have hs : support0200 = fromList transition1453Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1453Chunk0]
  have hn : (transition1453Raw0 : Multiset ℕ) = 1 • (supportNumbers0286 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0286] using hm

private def transition1454Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 540, 541, 542, 543, 648, 649, 650, 651]
private def transition1454Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private theorem transition1454Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1454Input0) = fromList transition1454Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1454 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0200 = 1 • support0285 := by
  have hs : support0200 = fromList transition1454Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1454Chunk0]
  have hn : (transition1454Raw0 : Multiset ℕ) = 1 • (supportNumbers0285 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0285] using hm

private def transition1455Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition1455Raw0 : List ℕ := [0, 1, 148, 149, 30, 31, 138, 139]
private theorem transition1455Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1455Input0) = fromList transition1455Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1455 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0285 = 1 • support1347 := by
  have hs : support0285 = fromList transition1455Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1455Chunk0]
  have hn : (transition1455Raw0 : Multiset ℕ) = 1 • (supportNumbers1347 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1347] using hm

private def transition1456Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition1456Raw0 : List ℕ := [0, 1, 578, 579, 148, 149, 726, 727, 604, 605, 30, 31, 712, 713, 138, 139]
private theorem transition1456Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1456Input0) = fromList transition1456Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1456 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0285 = 1 • support1348 := by
  have hs : support0285 = fromList transition1456Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1456Chunk0]
  have hn : (transition1456Raw0 : Multiset ℕ) = 1 • (supportNumbers1348 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1348] using hm

private def transition1457Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 540, 541, 542, 543, 648, 649, 650, 651]
private def transition1457Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1457Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1457Input0) = fromList transition1457Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1457 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0200 = 1 • support1350 := by
  have hs : support0200 = fromList transition1457Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1457Chunk0]
  have hn : (transition1457Raw0 : Multiset ℕ) = 1 • (supportNumbers1350 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1350] using hm

private def transition1458Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 544, 545, 546, 547, 692, 693, 694, 695, 828, 829, 830, 831, 936, 937, 938, 939]
private def transition1458Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139, 288, 289, 290, 291, 436, 437, 438, 439, 316, 317, 318, 319, 424, 425, 426, 427]
private theorem transition1458Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1458Input0) = fromList transition1458Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1458 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1350 = 1 • support0579 := by
  have hs : support1350 = fromList transition1458Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1458Chunk0]
  have hn : (transition1458Raw0 : Multiset ℕ) = 1 • (supportNumbers0579 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0579] using hm

private def transition1459Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 544, 545, 546, 547, 692, 693, 694, 695, 828, 829, 830, 831, 936, 937, 938, 939]
private def transition1459Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition1459Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1459Input0) = fromList transition1459Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1459 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1350 = 1 • support0581 := by
  have hs : support1350 = fromList transition1459Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1459Chunk0]
  have hn : (transition1459Raw0 : Multiset ℕ) = 1 • (supportNumbers0581 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0581] using hm

private def transition1460Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition1460Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition1460Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1460Input0) = fromList transition1460Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1460 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0201 = 1 • support0123 := by
  have hs : support0201 = fromList transition1460Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1460Chunk0]
  have hn : (transition1460Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition1461Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition1461Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 148, 149, 150, 151, 540, 541, 542, 543, 640, 641, 642, 643, 8, 9, 10, 11, 532, 533, 534, 535, 156, 157, 158, 159]
private theorem transition1461Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1461Input0) = fromList transition1461Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1461 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0201 = 1 • support0287 := by
  have hs : support0201 = fromList transition1461Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1461Chunk0]
  have hn : (transition1461Raw0 : Multiset ℕ) = 1 • (supportNumbers0287 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0287] using hm

private def transition1462Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition1462Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 8, 9, 10, 11, 156, 157, 158, 159]
private theorem transition1462Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1462Input0) = fromList transition1462Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1462 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0201 = 1 • support0123 := by
  have hs : support0201 = fromList transition1462Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1462Chunk0]
  have hn : (transition1462Raw0 : Multiset ℕ) = 1 • (supportNumbers0123 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0123] using hm

private def transition1463Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition1463Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 148, 149, 150, 151, 700, 701, 702, 703, 544, 545, 546, 547, 8, 9, 10, 11, 692, 693, 694, 695, 156, 157, 158, 159]
private theorem transition1463Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1463Input0) = fromList transition1463Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1463 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0201 = 1 • support1351 := by
  have hs : support0201 = fromList transition1463Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1463Chunk0]
  have hn : (transition1463Raw0 : Multiset ℕ) = 1 • (supportNumbers1351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1351] using hm

private def transition1464Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition1464Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition1464Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1464Input0) = fromList transition1464Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1464 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1351 = 1 • support1116 := by
  have hs : support1351 = fromList transition1464Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1464Chunk0]
  have hn : (transition1464Raw0 : Multiset ℕ) = 1 • (supportNumbers1116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1116] using hm

private def transition1465Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition1465Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition1465Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1465Input0) = fromList transition1465Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1465 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1351 = 1 • support1118 := by
  have hs : support1351 = fromList transition1465Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1465Chunk0]
  have hn : (transition1465Raw0 : Multiset ℕ) = 1 • (supportNumbers1118 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1118] using hm

private def transition1466Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1466Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1466Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1466Input0) = fromList transition1466Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1466 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0202 = 2 • support0288 := by
  have hs : support0202 = fromList transition1466Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1466Chunk0]
  have hn : (transition1466Raw0 : Multiset ℕ) = 2 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition1467Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1467Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1467Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1467Input0) = fromList transition1467Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1467 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0202 = 2 • support0289 := by
  have hs : support0202 = fromList transition1467Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1467Chunk0]
  have hn : (transition1467Raw0 : Multiset ℕ) = 2 • (supportNumbers0289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0289] using hm

private def transition1468Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1468Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1468Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1468Input0) = fromList transition1468Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1468 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0202 = 2 • support0288 := by
  have hs : support0202 = fromList transition1468Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1468Chunk0]
  have hn : (transition1468Raw0 : Multiset ℕ) = 2 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition1469Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition1469Raw0 : List ℕ := [0, 1, 8, 9, 148, 149, 156, 157, 22, 23, 30, 31, 130, 131, 138, 139]
private theorem transition1469Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1469Input0) = fromList transition1469Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1469 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0288 = 1 • support1352 := by
  have hs : support0288 = fromList transition1469Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1469Chunk0]
  have hn : (transition1469Raw0 : Multiset ℕ) = 1 • (supportNumbers1352 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1352] using hm

private def transition1470Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition1470Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 148, 149, 726, 727, 156, 157, 734, 735, 596, 597, 22, 23, 604, 605, 30, 31, 704, 705, 130, 131, 712, 713, 138, 139]
private theorem transition1470Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1470Input0) = fromList transition1470Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1470 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0288 = 1 • support1353 := by
  have hs : support0288 = fromList transition1470Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1470Chunk0]
  have hn : (transition1470Raw0 : Multiset ℕ) = 1 • (supportNumbers1353 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1353] using hm

private def transition1471Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 404, 405, 406, 407, 412, 413, 414, 415, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1471Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1471Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1471Input0) = fromList transition1471Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1471 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0202 = 2 • support1355 := by
  have hs : support0202 = fromList transition1471Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1471Chunk0]
  have hn : (transition1471Raw0 : Multiset ℕ) = 2 • (supportNumbers1355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1355] using hm

private def transition1472Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 544, 545, 546, 547, 552, 553, 554, 555, 692, 693, 694, 695, 700, 701, 702, 703, 820, 821, 822, 823, 828, 829, 830, 831, 928, 929, 930, 931, 936, 937, 938, 939]
private def transition1472Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 288, 289, 290, 291, 296, 297, 298, 299, 436, 437, 438, 439, 444, 445, 446, 447, 308, 309, 310, 311, 316, 317, 318, 319, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition1472Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1472Input0) = fromList transition1472Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1472 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1355 = 1 • support0506 := by
  have hs : support1355 = fromList transition1472Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1472Chunk0]
  have hn : (transition1472Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
