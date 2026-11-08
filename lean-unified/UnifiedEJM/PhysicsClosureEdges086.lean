import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1579Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1579Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718]
private theorem transition1579Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1579Input0) = fromList transition1579Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1579 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0217 = 1 • support0306 := by
  have hs : support0217 = fromList transition1579Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1579Chunk0]
  have hn : (transition1579Raw0 : Multiset ℕ) = 1 • (supportNumbers0306 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0306] using hm

private def transition1580Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1580Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private theorem transition1580Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1580Input0) = fromList transition1580Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1580 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0217 = 1 • support0217 := by
  have hs : support0217 = fromList transition1580Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1580Chunk0]
  have hn : (transition1580Raw0 : Multiset ℕ) = 1 • (supportNumbers0217 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0217] using hm

private def transition1581Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78]
private def transition1581Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622]
private theorem transition1581Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1581Input0) = fromList transition1581Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1581 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0217 = 1 • support1390 := by
  have hs : support0217 = fromList transition1581Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1581Chunk0]
  have hn : (transition1581Raw0 : Multiset ℕ) = 1 • (supportNumbers1390 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1390] using hm

private def transition1582Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622]
private def transition1582Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366]
private theorem transition1582Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1582Input0) = fromList transition1582Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1582 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1390 = 1 • support0935 := by
  have hs : support1390 = fromList transition1582Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1582Chunk0]
  have hn : (transition1582Raw0 : Multiset ℕ) = 1 • (supportNumbers0935 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0935] using hm

private def transition1583Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622]
private def transition1583Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814]
private theorem transition1583Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1583Input0) = fromList transition1583Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1583 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1390 = 1 • support0937 := by
  have hs : support1390 = fromList transition1583Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1583Chunk0]
  have hn : (transition1583Raw0 : Multiset ℕ) = 1 • (supportNumbers0937 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0937] using hm

private def transition1584Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1584Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1584Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1584Input0) = fromList transition1584Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1584 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0218 = 1 • support0040 := by
  have hs : support0218 = fromList transition1584Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1584Chunk0]
  have hn : (transition1584Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition1585Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1585Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 512, 514, 516, 518, 137, 139, 141, 143, 577, 579, 581, 583, 200, 202, 204, 206]
private theorem transition1585Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1585Input0) = fromList transition1585Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1585 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0218 = 1 • support0307 := by
  have hs : support0218 = fromList transition1585Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1585Chunk0]
  have hn : (transition1585Raw0 : Multiset ℕ) = 1 • (supportNumbers0307 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0307] using hm

private def transition1586Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1586Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206]
private theorem transition1586Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1586Input0) = fromList transition1586Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1586 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0218 = 1 • support0040 := by
  have hs : support0218 = fromList transition1586Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1586Chunk0]
  have hn : (transition1586Raw0 : Multiset ℕ) = 1 • (supportNumbers0040 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0040] using hm

private def transition1587Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1587Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 672, 674, 676, 678, 137, 139, 141, 143, 737, 739, 741, 743, 200, 202, 204, 206]
private theorem transition1587Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1587Input0) = fromList transition1587Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1587 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0218 = 1 • support1391 := by
  have hs : support0218 = fromList transition1587Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1587Chunk0]
  have hn : (transition1587Raw0 : Multiset ℕ) = 1 • (supportNumbers1391 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1391] using hm

private def transition1588Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 553, 555, 557, 559, 616, 618, 620, 622, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition1588Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 297, 299, 301, 303, 360, 362, 364, 366, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition1588Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1588Input0) = fromList transition1588Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1588 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1391 = 1 • support1392 := by
  have hs : support1391 = fromList transition1588Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1588Chunk0]
  have hn : (transition1588Raw0 : Multiset ℕ) = 1 • (supportNumbers1392 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1392] using hm

private def transition1589Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 553, 555, 557, 559, 616, 618, 620, 622, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition1589Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition1589Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1589Input0) = fromList transition1589Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1589 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1391 = 1 • support1394 := by
  have hs : support1391 = fromList transition1589Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1589Chunk0]
  have hn : (transition1589Raw0 : Multiset ℕ) = 1 • (supportNumbers1394 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1394] using hm

private def transition1590Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846]
private def transition1590Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private theorem transition1590Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1590Input0) = fromList transition1590Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1590 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0219 = 1 • support0308 := by
  have hs : support0219 = fromList transition1590Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1590Chunk0]
  have hn : (transition1590Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition1591Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846]
private def transition1591Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 128, 512, 130, 514, 132, 516, 134, 518, 137, 521, 139, 523, 141, 525, 143, 527, 193, 577, 195, 579, 197, 581, 199, 583, 200, 584, 202, 586, 204, 588, 206, 590, 384, 768, 386, 770, 388, 772, 390, 774, 393, 777, 395, 779, 397, 781, 399, 783, 449, 833, 451, 835, 453, 837, 455, 839, 456, 840, 458, 842, 460, 844, 462, 846, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974]
private theorem transition1591Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1591Input0) = fromList transition1591Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1591 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0219 = 1 • support0309 := by
  have hs : support0219 = fromList transition1591Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1591Chunk0]
  have hn : (transition1591Raw0 : Multiset ℕ) = 1 • (supportNumbers0309 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0309] using hm

private def transition1592Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846]
private def transition1592Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334]
private theorem transition1592Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1592Input0) = fromList transition1592Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1592 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0219 = 1 • support0308 := by
  have hs : support0219 = fromList transition1592Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1592Chunk0]
  have hn : (transition1592Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition1593Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1593Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 128, 132, 137, 141, 193, 197, 200, 204, 2, 6, 11, 15, 67, 71, 74, 78, 130, 134, 139, 143, 195, 199, 202, 206]
private theorem transition1593Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1593Input0) = fromList transition1593Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1593 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0308 = 1 • support0388 := by
  have hs : support0308 = fromList transition1593Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1593Chunk0]
  have hn : (transition1593Raw0 : Multiset ℕ) = 1 • (supportNumbers0388 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0388] using hm

private def transition1594Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1594Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 128, 706, 132, 710, 137, 715, 141, 719, 193, 643, 197, 647, 200, 650, 204, 654, 576, 2, 580, 6, 585, 11, 589, 15, 513, 67, 517, 71, 520, 74, 524, 78, 704, 130, 708, 134, 713, 139, 717, 143, 641, 195, 645, 199, 648, 202, 652, 206]
private theorem transition1594Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1594Input0) = fromList transition1594Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1594 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0308 = 1 • support1396 := by
  have hs : support0308 = fromList transition1594Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1594Chunk0]
  have hn : (transition1594Raw0 : Multiset ℕ) = 1 • (supportNumbers1396 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1396] using hm

private def transition1595Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718, 768, 770, 772, 774, 777, 779, 781, 783, 833, 835, 837, 839, 840, 842, 844, 846]
private def transition1595Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 128, 672, 130, 674, 132, 676, 134, 678, 137, 681, 139, 683, 141, 685, 143, 687, 193, 737, 195, 739, 197, 741, 199, 743, 200, 744, 202, 746, 204, 748, 206, 750, 384, 928, 386, 930, 388, 932, 390, 934, 393, 937, 395, 939, 397, 941, 399, 943, 449, 993, 451, 995, 453, 997, 455, 999, 456, 1000, 458, 1002, 460, 1004, 462, 1006, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878]
private theorem transition1595Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1595Input0) = fromList transition1595Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1595 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0219 = 1 • support1397 := by
  have hs : support0219 = fromList transition1595Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1595Chunk0]
  have hn : (transition1595Raw0 : Multiset ℕ) = 1 • (supportNumbers1397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1397] using hm

private def transition1596Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 384, 386, 388, 390, 393, 395, 397, 399, 449, 451, 453, 455, 456, 458, 460, 462]
private def transition1596Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem transition1596Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1596Input0) = fromList transition1596Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1596Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 672, 674, 676, 678, 681, 683, 685, 687, 737, 739, 741, 743, 744, 746, 748, 750, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878, 928, 930, 932, 934, 937, 939, 941, 943, 993, 995, 997, 999, 1000, 1002, 1004, 1006]
private def transition1596Raw1 : List ℕ := [288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 416, 418, 420, 422, 425, 427, 429, 431, 481, 483, 485, 487, 488, 490, 492, 494]
private theorem transition1596Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1596Input1) = fromList transition1596Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1596 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1397 = 2 • support1171 := by
  have hs : support1397 = fromList transition1596Input0 + fromList transition1596Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1596Chunk0, transition1596Chunk1]
  have hn : (transition1596Raw0 : Multiset ℕ) + (transition1596Raw1 : Multiset ℕ) = 2 • (supportNumbers1171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1171] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
