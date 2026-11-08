import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0580Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 288, 289, 290, 291, 436, 437, 438, 439]
private def finish0580Raw0 : List ℕ := [0, 1, 2, 3, 180, 181, 182, 183]
private theorem finish0580Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0580Input0) = fromList finish0580Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0580 : finishSupport ⟨false, bits4 4⟩ support1536 = 1 • support1537 := by
  have hs : support1536 = fromList finish0580Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0580Chunk0]
  have hn : (finish0580Raw0 : Multiset ℕ) = 1 • (supportNumbers1537 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1537] using hm

private def finish0581Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 288, 289, 290, 291, 436, 437, 438, 439, 576, 577, 578, 579, 724, 725, 726, 727, 864, 865, 866, 867, 1012, 1013, 1014, 1015]
private def finish0581Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 32, 33, 34, 35, 180, 181, 182, 183, 64, 65, 66, 67, 212, 213, 214, 215, 96, 97, 98, 99, 244, 245, 246, 247]
private theorem finish0581Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0581Input0) = fromList finish0581Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0581 : finishSupport ⟨true, bits4 4⟩ support1538 = 1 • support1539 := by
  have hs : support1538 = fromList finish0581Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0581Chunk0]
  have hn : (finish0581Raw0 : Multiset ℕ) = 1 • (supportNumbers1539 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1539] using hm

private def finish0582Input0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149]
private def finish0582Raw0 : List ℕ := [0, 1, 136, 137]
private theorem finish0582Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0582Input0) = fromList finish0582Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0582 : finishSupport ⟨false, bits4 4⟩ support1540 = 1 • support0584 := by
  have hs : support1540 = fromList finish0582Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0582Chunk0]
  have hn : (finish0582Raw0 : Multiset ℕ) = 1 • (supportNumbers0584 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0584] using hm

private def finish0583Input0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149, 578, 579, 606, 607, 714, 715, 726, 727]
private def finish0583Raw0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149, 66, 67, 94, 95, 202, 203, 214, 215]
private theorem finish0583Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0583Input0) = fromList finish0583Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0583 : finishSupport ⟨true, bits4 4⟩ support1541 = 1 • support1542 := by
  have hs : support1541 = fromList finish0583Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0583Chunk0]
  have hn : (finish0583Raw0 : Multiset ℕ) = 1 • (supportNumbers1542 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1542] using hm

private def finish0584Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def finish0584Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem finish0584Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0584Input0) = fromList finish0584Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0584 : finishSupport ⟨false, bits4 4⟩ support0374 = 1 • support0065 := by
  have hs : support0374 = fromList finish0584Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0584Chunk0]
  have hn : (finish0584Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def finish0585Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 576, 577, 578, 579, 604, 605, 606, 607, 712, 713, 714, 715, 724, 725, 726, 727]
private def finish0585Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 64, 65, 66, 67, 92, 93, 94, 95, 200, 201, 202, 203, 212, 213, 214, 215]
private theorem finish0585Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0585Input0) = fromList finish0585Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0585 : finishSupport ⟨true, bits4 4⟩ support1543 = 1 • support1544 := by
  have hs : support1543 = fromList finish0585Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0585Chunk0]
  have hn : (finish0585Raw0 : Multiset ℕ) = 1 • (supportNumbers1544 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1544] using hm

private def finish0586Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 296, 297, 298, 299, 308, 309, 310, 311, 416, 417, 418, 419, 444, 445, 446, 447]
private def finish0586Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 52, 53, 54, 55, 188, 189, 190, 191]
private theorem finish0586Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0586Input0) = fromList finish0586Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0586 : finishSupport ⟨false, bits4 4⟩ support1546 = 1 • support0713 := by
  have hs : support1546 = fromList finish0586Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0586Chunk0]
  have hn : (finish0586Raw0 : Multiset ℕ) = 1 • (supportNumbers0713 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0713] using hm

private def finish0587Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 296, 297, 298, 299, 308, 309, 310, 311, 416, 417, 418, 419, 444, 445, 446, 447, 576, 577, 578, 579, 604, 605, 606, 607, 712, 713, 714, 715, 724, 725, 726, 727, 872, 873, 874, 875, 884, 885, 886, 887, 992, 993, 994, 995, 1020, 1021, 1022, 1023]
private def finish0587Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151, 40, 41, 42, 43, 52, 53, 54, 55, 160, 161, 162, 163, 188, 189, 190, 191, 64, 65, 66, 67, 92, 93, 94, 95, 200, 201, 202, 203, 212, 213, 214, 215, 104, 105, 106, 107, 116, 117, 118, 119, 224, 225, 226, 227, 252, 253, 254, 255]
private theorem finish0587Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0587Input0) = fromList finish0587Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0587 : finishSupport ⟨true, bits4 4⟩ support1547 = 1 • support1548 := by
  have hs : support1547 = fromList finish0587Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0587Chunk0]
  have hn : (finish0587Raw0 : Multiset ℕ) = 1 • (supportNumbers1548 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1548] using hm

private def finish0588Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 416, 417, 418, 419, 436, 437, 438, 439]
private def finish0588Raw0 : List ℕ := [0, 1, 2, 3, 180, 181, 182, 183]
private theorem finish0588Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0588Input0) = fromList finish0588Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0588 : finishSupport ⟨false, bits4 4⟩ support1550 = 1 • support1537 := by
  have hs : support1550 = fromList finish0588Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0588Chunk0]
  have hn : (finish0588Raw0 : Multiset ℕ) = 1 • (supportNumbers1537 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1537] using hm

private def finish0589Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 416, 417, 418, 419, 436, 437, 438, 439, 576, 577, 578, 579, 596, 597, 598, 599, 992, 993, 994, 995, 1012, 1013, 1014, 1015]
private def finish0589Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 160, 161, 162, 163, 180, 181, 182, 183, 64, 65, 66, 67, 84, 85, 86, 87, 224, 225, 226, 227, 244, 245, 246, 247]
private theorem finish0589Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0589Input0) = fromList finish0589Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0589 : finishSupport ⟨true, bits4 4⟩ support1551 = 1 • support1552 := by
  have hs : support1551 = fromList finish0589Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0589Chunk0]
  have hn : (finish0589Raw0 : Multiset ℕ) = 1 • (supportNumbers1552 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1552] using hm

private def finish0590Input0 : List ℕ := [0, 1, 20, 21, 138, 139, 158, 159]
private def finish0590Raw0 : List ℕ := [0, 1, 138, 139]
private theorem finish0590Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0590Input0) = fromList finish0590Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0590 : finishSupport ⟨false, bits4 4⟩ support1554 = 1 • support0575 := by
  have hs : support1554 = fromList finish0590Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0590Chunk0]
  have hn : (finish0590Raw0 : Multiset ℕ) = 1 • (supportNumbers0575 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0575] using hm

private def finish0591Input0 : List ℕ := [0, 1, 20, 21, 138, 139, 158, 159, 578, 579, 598, 599, 712, 713, 732, 733]
private def finish0591Raw0 : List ℕ := [0, 1, 20, 21, 138, 139, 158, 159, 66, 67, 86, 87, 200, 201, 220, 221]
private theorem finish0591Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0591Input0) = fromList finish0591Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0591 : finishSupport ⟨true, bits4 4⟩ support1555 = 1 • support1556 := by
  have hs : support1555 = fromList finish0591Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0591Chunk0]
  have hn : (finish0591Raw0 : Multiset ℕ) = 1 • (supportNumbers1556 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1556] using hm

private def finish0592Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 296, 298, 300, 302, 361, 363, 365, 367, 416, 418, 420, 422, 481, 483, 485, 487]
private def finish0592Raw0 : List ℕ := [0, 2, 65, 67, 136, 138, 201, 203, 44, 46, 109, 111, 164, 166, 229, 231]
private theorem finish0592Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0592Input0) = fromList finish0592Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0592 : finishSupport ⟨false, bits4 4⟩ support1559 = 1 • support1560 := by
  have hs : support1559 = fromList finish0592Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0592Chunk0]
  have hn : (finish0592Raw0 : Multiset ℕ) = 1 • (supportNumbers1560 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1560] using hm

private def finish0593Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 296, 298, 300, 302, 361, 363, 365, 367, 416, 418, 420, 422, 481, 483, 485, 487, 513, 515, 517, 519, 576, 578, 580, 582, 649, 651, 653, 655, 712, 714, 716, 718, 809, 811, 813, 815, 872, 874, 876, 878, 929, 931, 933, 935, 992, 994, 996, 998]
private def finish0593Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 40, 42, 44, 46, 105, 107, 109, 111, 160, 162, 164, 166, 225, 227, 229, 231, 1, 3, 5, 7, 64, 66, 68, 70, 137, 139, 141, 143, 200, 202, 204, 206, 41, 43, 45, 47, 104, 106, 108, 110, 161, 163, 165, 167, 224, 226, 228, 230]
private theorem finish0593Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0593Input0) = fromList finish0593Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0593 : finishSupport ⟨true, bits4 4⟩ support1561 = 1 • support0612 := by
  have hs : support1561 = fromList finish0593Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0593Chunk0]
  have hn : (finish0593Raw0 : Multiset ℕ) = 1 • (supportNumbers0612 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0612] using hm

private def finish0594Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 128, 132, 138, 142, 193, 197, 203, 207]
private def finish0594Raw0 : List ℕ := [0, 10, 65, 75, 128, 138, 193, 203]
private theorem finish0594Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0594Input0) = fromList finish0594Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0594 : finishSupport ⟨false, bits4 4⟩ support1562 = 1 • support1563 := by
  have hs : support1562 = fromList finish0594Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0594Chunk0]
  have hn : (finish0594Raw0 : Multiset ℕ) = 1 • (supportNumbers1563 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1563] using hm

private def finish0595Input0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 128, 132, 138, 142, 193, 197, 203, 207, 515, 519, 521, 525, 578, 582, 584, 588, 643, 647, 649, 653, 706, 710, 712, 716]
private def finish0595Raw0 : List ℕ := [0, 4, 10, 14, 65, 69, 75, 79, 128, 132, 138, 142, 193, 197, 203, 207, 3, 7, 9, 13, 66, 70, 72, 76, 131, 135, 137, 141, 194, 198, 200, 204]
private theorem finish0595Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0595Input0) = fromList finish0595Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0595 : finishSupport ⟨true, bits4 4⟩ support1564 = 1 • support1565 := by
  have hs : support1564 = fromList finish0595Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0595Chunk0]
  have hn : (finish0595Raw0 : Multiset ℕ) = 1 • (supportNumbers1565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1565] using hm

private def finish0596Input0 : List ℕ := [0, 4, 65, 69, 139, 143, 202, 206]
private def finish0596Raw0 : List ℕ := [0, 65, 139, 202]
private theorem finish0596Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0596Input0) = fromList finish0596Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0596 : finishSupport ⟨false, bits4 4⟩ support1567 = 1 • support1568 := by
  have hs : support1567 = fromList finish0596Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0596Chunk0]
  have hn : (finish0596Raw0 : Multiset ℕ) = 1 • (supportNumbers1568 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1568] using hm

private def finish0597Input0 : List ℕ := [0, 4, 65, 69, 139, 143, 202, 206, 515, 519, 578, 582, 648, 652, 713, 717]
private def finish0597Raw0 : List ℕ := [0, 4, 65, 69, 139, 143, 202, 206, 3, 7, 66, 70, 136, 140, 201, 205]
private theorem finish0597Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0597Input0) = fromList finish0597Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0597 : finishSupport ⟨true, bits4 4⟩ support1569 = 1 • support0729 := by
  have hs : support1569 = fromList finish0597Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0597Chunk0]
  have hn : (finish0597Raw0 : Multiset ℕ) = 1 • (supportNumbers0729 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0729] using hm

private def finish0598Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494]
private def finish0598Raw0 : List ℕ := [0, 2, 65, 67, 137, 139, 200, 202, 36, 38, 101, 103, 173, 175, 236, 238]
private theorem finish0598Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0598Input0) = fromList finish0598Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0598 : finishSupport ⟨false, bits4 4⟩ support1571 = 1 • support1572 := by
  have hs : support1571 = fromList finish0598Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0598Chunk0]
  have hn : (finish0598Raw0 : Multiset ℕ) = 1 • (supportNumbers1572 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1572] using hm

private def finish0599Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 425, 427, 429, 431, 488, 490, 492, 494, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719, 801, 803, 805, 807, 864, 866, 868, 870, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def finish0599Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 32, 34, 36, 38, 97, 99, 101, 103, 169, 171, 173, 175, 232, 234, 236, 238, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 33, 35, 37, 39, 96, 98, 100, 102, 168, 170, 172, 174, 233, 235, 237, 239]
private theorem finish0599Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0599Input0) = fromList finish0599Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0599 : finishSupport ⟨true, bits4 4⟩ support1573 = 1 • support0604 := by
  have hs : support1573 = fromList finish0599Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0599Chunk0]
  have hn : (finish0599Raw0 : Multiset ℕ) = 1 • (supportNumbers0604 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0604] using hm

private def finish0600Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private def finish0600Raw0 : List ℕ := [0, 2, 65, 67, 137, 139, 200, 202]
private theorem finish0600Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0600Input0) = fromList finish0600Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0600 : finishSupport ⟨false, bits4 4⟩ support0040 = 1 • support1574 := by
  have hs : support0040 = fromList finish0600Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0600Chunk0]
  have hn : (finish0600Raw0 : Multiset ℕ) = 1 • (supportNumbers1574 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1574] using hm

private def finish0601Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 513, 515, 517, 519, 576, 578, 580, 582, 648, 650, 652, 654, 713, 715, 717, 719]
private def finish0601Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem finish0601Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0601Input0) = fromList finish0601Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0601 : finishSupport ⟨true, bits4 4⟩ support0041 = 1 • support0088 := by
  have hs : support0041 = fromList finish0601Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0601Chunk0]
  have hn : (finish0601Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def finish0602Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 128, 132, 137, 141, 193, 197, 200, 204]
private def finish0602Raw0 : List ℕ := [0, 9, 65, 72, 128, 137, 193, 200]
private theorem finish0602Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0602Input0) = fromList finish0602Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0602 : finishSupport ⟨false, bits4 4⟩ support1576 = 1 • support1577 := by
  have hs : support1576 = fromList finish0602Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0602Chunk0]
  have hn : (finish0602Raw0 : Multiset ℕ) = 1 • (supportNumbers1577 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1577] using hm

private def finish0603Input0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 128, 132, 137, 141, 193, 197, 200, 204, 515, 519, 522, 526, 578, 582, 587, 591, 643, 647, 650, 654, 706, 710, 715, 719]
private def finish0603Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 128, 132, 137, 141, 193, 197, 200, 204, 3, 7, 10, 14, 66, 70, 75, 79, 131, 135, 138, 142, 194, 198, 203, 207]
private theorem finish0603Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0603Input0) = fromList finish0603Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0603 : finishSupport ⟨true, bits4 4⟩ support1578 = 1 • support1565 := by
  have hs : support1578 = fromList finish0603Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0603Chunk0]
  have hn : (finish0603Raw0 : Multiset ℕ) = 1 • (supportNumbers1565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1565] using hm

private def finish0604Input0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79]
private def finish0604Raw0 : List ℕ := [0, 3, 9, 10, 65, 66, 72, 75]
private theorem finish0604Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0604Input0) = fromList finish0604Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0604 : finishSupport ⟨false, bits4 4⟩ support1151 = 1 • support1500 := by
  have hs : support1151 = fromList finish0604Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0604Chunk0]
  have hn : (finish0604Raw0 : Multiset ℕ) = 1 • (supportNumbers1500 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1500] using hm

private def finish0605Input0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 512, 515, 516, 519, 521, 522, 525, 526, 577, 578, 581, 582, 584, 587, 588, 591]
private def finish0605Raw0 : List ℕ := [0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79, 0, 3, 4, 7, 9, 10, 13, 14, 65, 66, 69, 70, 72, 75, 76, 79]
private theorem finish0605Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0605Input0) = fromList finish0605Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0605 : finishSupport ⟨true, bits4 4⟩ support1580 = 2 • support1151 := by
  have hs : support1580 = fromList finish0605Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0605Chunk0]
  have hn : (finish0605Raw0 : Multiset ℕ) = 2 • (supportNumbers1151 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1151] using hm

private def finish0606Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 138, 139, 142, 143, 202, 203, 206, 207]
private def finish0606Raw0 : List ℕ := [0, 1, 64, 65, 138, 139, 202, 203]
private theorem finish0606Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0606Input0) = fromList finish0606Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0606 : finishSupport ⟨false, bits4 4⟩ support1582 = 1 • support1583 := by
  have hs : support1582 = fromList finish0606Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0606Chunk0]
  have hn : (finish0606Raw0 : Multiset ℕ) = 1 • (supportNumbers1583 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1583] using hm

private def finish0607Input0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 138, 139, 142, 143, 202, 203, 206, 207, 514, 515, 518, 519, 578, 579, 582, 583, 648, 649, 652, 653, 712, 713, 716, 717]
private def finish0607Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 138, 139, 142, 143, 202, 203, 206, 207, 2, 3, 6, 7, 66, 67, 70, 71, 136, 137, 140, 141, 200, 201, 204, 205]
private theorem finish0607Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0607Input0) = fromList finish0607Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0607 : finishSupport ⟨true, bits4 4⟩ support1584 = 1 • support0088 := by
  have hs : support1584 = fromList finish0607Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0607Chunk0]
  have hn : (finish0607Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def finish0608Input0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 129, 130, 133, 134, 192, 195, 196, 199]
private def finish0608Raw0 : List ℕ := [0, 3, 65, 66, 129, 130, 192, 195]
private theorem finish0608Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0608Input0) = fromList finish0608Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0608 : finishSupport ⟨false, bits4 4⟩ support0908 = 1 • support1508 := by
  have hs : support0908 = fromList finish0608Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0608Chunk0]
  have hn : (finish0608Raw0 : Multiset ℕ) = 1 • (supportNumbers1508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1508] using hm

private def finish0609Input0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 129, 130, 133, 134, 192, 195, 196, 199, 512, 515, 516, 519, 577, 578, 581, 582, 641, 642, 645, 646, 704, 707, 708, 711]
private def finish0609Raw0 : List ℕ := [0, 3, 4, 7, 65, 66, 69, 70, 129, 130, 133, 134, 192, 195, 196, 199, 0, 3, 4, 7, 65, 66, 69, 70, 129, 130, 133, 134, 192, 195, 196, 199]
private theorem finish0609Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0609Input0) = fromList finish0609Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0609 : finishSupport ⟨true, bits4 4⟩ support1587 = 2 • support0908 := by
  have hs : support1587 = fromList finish0609Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0609Chunk0]
  have hn : (finish0609Raw0 : Multiset ℕ) = 2 • (supportNumbers0908 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0908] using hm

private def finish0610Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 296, 298, 300, 302, 361, 363, 365, 367, 425, 427, 429, 431, 488, 490, 492, 494]
private def finish0610Raw0 : List ℕ := [0, 2, 65, 67, 129, 131, 192, 194, 44, 46, 109, 111, 173, 175, 236, 238]
private theorem finish0610Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0610Input0) = fromList finish0610Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0610 : finishSupport ⟨false, bits4 4⟩ support1590 = 1 • support1591 := by
  have hs : support1590 = fromList finish0610Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0610Chunk0]
  have hn : (finish0610Raw0 : Multiset ℕ) = 1 • (supportNumbers1591 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1591] using hm

private def finish0611Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 296, 298, 300, 302, 361, 363, 365, 367, 425, 427, 429, 431, 488, 490, 492, 494, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 809, 811, 813, 815, 872, 874, 876, 878, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def finish0611Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 40, 42, 44, 46, 105, 107, 109, 111, 169, 171, 173, 175, 232, 234, 236, 238, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 41, 43, 45, 47, 104, 106, 108, 110, 168, 170, 172, 174, 233, 235, 237, 239]
private theorem finish0611Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0611Input0) = fromList finish0611Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0611 : finishSupport ⟨true, bits4 4⟩ support1592 = 1 • support0954 := by
  have hs : support1592 = fromList finish0611Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0611Chunk0]
  have hn : (finish0611Raw0 : Multiset ℕ) = 1 • (supportNumbers0954 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0954] using hm

private def finish0612Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 130, 131, 134, 135, 154, 155, 158, 159, 194, 195, 198, 199, 218, 219, 222, 223]
private def finish0612Raw0 : List ℕ := [0, 1, 24, 25, 64, 65, 88, 89, 130, 131, 154, 155, 194, 195, 218, 219]
private theorem finish0612Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0612Input0) = fromList finish0612Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0612 : finishSupport ⟨false, bits4 4⟩ support1597 = 1 • support1598 := by
  have hs : support1597 = fromList finish0612Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0612Chunk0]
  have hn : (finish0612Raw0 : Multiset ℕ) = 1 • (supportNumbers1598 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1598] using hm

private def finish0613Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 130, 131, 134, 135, 154, 155, 158, 159, 194, 195, 198, 199, 218, 219, 222, 223, 514, 515, 518, 519, 538, 539, 542, 543, 578, 579, 582, 583, 602, 603, 606, 607, 640, 641, 644, 645, 664, 665, 668, 669, 704, 705, 708, 709, 728, 729, 732, 733]
private def finish0613Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 130, 131, 134, 135, 154, 155, 158, 159, 194, 195, 198, 199, 218, 219, 222, 223, 2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95, 128, 129, 132, 133, 152, 153, 156, 157, 192, 193, 196, 197, 216, 217, 220, 221]
private theorem finish0613Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0613Input0) = fromList finish0613Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0613 : finishSupport ⟨true, bits4 4⟩ support1599 = 1 • support0326 := by
  have hs : support1599 = fromList finish0613Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0613Chunk0]
  have hn : (finish0613Raw0 : Multiset ℕ) = 1 • (supportNumbers0326 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0326] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
