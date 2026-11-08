import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1506Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition1506Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439]
private theorem transition1506Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1506Input0) = fromList transition1506Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1506 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1370 = 1 • support1360 := by
  have hs : support1370 = fromList transition1506Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1506Chunk0]
  have hn : (transition1506Raw0 : Multiset ℕ) = 1 • (supportNumbers1360 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1360] using hm

private def transition1507Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695]
private def transition1507Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition1507Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1507Input0) = fromList transition1507Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1507 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1370 = 1 • support1362 := by
  have hs : support1370 = fromList transition1507Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1507Chunk0]
  have hn : (transition1507Raw0 : Multiset ℕ) = 1 • (supportNumbers1362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1362] using hm

private def transition1508Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition1508Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition1508Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1508Input0) = fromList transition1508Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1508 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0206 = 1 • support0073 := by
  have hs : support0206 = fromList transition1508Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1508Chunk0]
  have hn : (transition1508Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition1509Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition1509Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition1509Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1509Input0) = fromList transition1509Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1509 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0206 = 1 • support0073 := by
  have hs : support0206 = fromList transition1509Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1509Chunk0]
  have hn : (transition1509Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition1510Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition1510Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition1510Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1510Input0) = fromList transition1510Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1510 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0206 = 1 • support0073 := by
  have hs : support0206 = fromList transition1510Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1510Chunk0]
  have hn : (transition1510Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition1511Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition1511Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159]
private theorem transition1511Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1511Input0) = fromList transition1511Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1511 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0206 = 1 • support0073 := by
  have hs : support0206 = fromList transition1511Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1511Chunk0]
  have hn : (transition1511Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition1512Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition1512Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition1512Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1512Input0) = fromList transition1512Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1512 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0073 = 1 • support0073 := by
  have hs : support0073 = fromList transition1512Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1512Chunk0]
  have hn : (transition1512Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition1513Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition1513Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735]
private theorem transition1513Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1513Input0) = fromList transition1513Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1513 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0073 = 1 • support0591 := by
  have hs : support0073 = fromList transition1513Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1513Chunk0]
  have hn : (transition1513Raw0 : Multiset ℕ) = 1 • (supportNumbers0591 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0591] using hm

private def transition1514Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition1514Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition1514Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1514Input0) = fromList transition1514Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1514 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0207 = 1 • support0036 := by
  have hs : support0207 = fromList transition1514Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1514Chunk0]
  have hn : (transition1514Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition1515Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition1515Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 8, 648, 9, 649, 10, 650, 11, 651, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition1515Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1515Input0) = fromList transition1515Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1515 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0207 = 1 • support0037 := by
  have hs : support0207 = fromList transition1515Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1515Chunk0]
  have hn : (transition1515Raw0 : Multiset ℕ) = 1 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition1516Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition1516Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition1516Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1516Input0) = fromList transition1516Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1516 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0207 = 1 • support0036 := by
  have hs : support0207 = fromList transition1516Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1516Chunk0]
  have hn : (transition1516Raw0 : Multiset ℕ) = 1 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition1517Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663, 776, 777, 778, 779, 796, 797, 798, 799, 904, 905, 906, 907, 924, 925, 926, 927]
private def transition1517Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 8, 552, 9, 553, 10, 554, 11, 555, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition1517Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1517Input0) = fromList transition1517Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1517 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0207 = 1 • support0593 := by
  have hs : support0207 = fromList transition1517Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1517Chunk0]
  have hn : (transition1517Raw0 : Multiset ℕ) = 1 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition1518Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 512, 514, 516, 518, 577, 579, 581, 583]
private def transition1518Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private theorem transition1518Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1518Input0) = fromList transition1518Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1518 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0208 = 1 • support0297 := by
  have hs : support0208 = fromList transition1518Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1518Chunk0]
  have hn : (transition1518Raw0 : Multiset ℕ) = 1 • (supportNumbers0297 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0297] using hm

private def transition1519Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 512, 514, 516, 518, 577, 579, 581, 583]
private def transition1519Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967]
private theorem transition1519Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1519Input0) = fromList transition1519Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1519 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0208 = 1 • support0298 := by
  have hs : support0208 = fromList transition1519Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1519Chunk0]
  have hn : (transition1519Raw0 : Multiset ℕ) = 1 • (supportNumbers0298 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0298] using hm

private def transition1520Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 512, 514, 516, 518, 577, 579, 581, 583]
private def transition1520Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private theorem transition1520Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1520Input0) = fromList transition1520Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1520 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0208 = 1 • support0297 := by
  have hs : support0208 = fromList transition1520Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1520Chunk0]
  have hn : (transition1520Raw0 : Multiset ℕ) = 1 • (supportNumbers0297 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0297] using hm

private def transition1521Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition1521Raw0 : List ℕ := [0, 4, 65, 69, 2, 6, 67, 71]
private theorem transition1521Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1521Input0) = fromList transition1521Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1521 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0297 = 1 • support0016 := by
  have hs : support0297 = fromList transition1521Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1521Chunk0]
  have hn : (transition1521Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition1522Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327]
private def transition1522Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 576, 2, 580, 6, 513, 67, 517, 71]
private theorem transition1522Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1522Input0) = fromList transition1522Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1522 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0297 = 1 • support0595 := by
  have hs : support0297 = fromList transition1522Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1522Chunk0]
  have hn : (transition1522Raw0 : Multiset ℕ) = 1 • (supportNumbers0595 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0595] using hm

private def transition1523Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 512, 514, 516, 518, 577, 579, 581, 583]
private def transition1523Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871]
private theorem transition1523Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1523Input0) = fromList transition1523Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1523 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0208 = 1 • support1371 := by
  have hs : support0208 = fromList transition1523Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1523Chunk0]
  have hn : (transition1523Raw0 : Multiset ℕ) = 1 • (supportNumbers1371 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1371] using hm

private def transition1524Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 544, 546, 548, 550, 609, 611, 613, 615, 800, 802, 804, 806, 865, 867, 869, 871]
private def transition1524Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 0, 2, 4, 6, 65, 67, 69, 71, 288, 290, 292, 294, 353, 355, 357, 359, 288, 290, 292, 294, 353, 355, 357, 359]
private theorem transition1524Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1524Input0) = fromList transition1524Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1524 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1371 = 2 • support0722 := by
  have hs : support1371 = fromList transition1524Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1524Chunk0]
  have hn : (transition1524Raw0 : Multiset ℕ) = 2 • (supportNumbers0722 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0722] using hm

private def transition1525Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 256, 258, 260, 262, 321, 323, 325, 327, 544, 546, 548, 550, 609, 611, 613, 615, 800, 802, 804, 806, 865, 867, 869, 871]
private def transition1525Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807]
private theorem transition1525Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1525Input0) = fromList transition1525Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1525 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1371 = 2 • support0724 := by
  have hs : support1371 = fromList transition1525Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1525Chunk0]
  have hn : (transition1525Raw0 : Multiset ℕ) = 2 • (supportNumbers0724 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0724] using hm

private def transition1526Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1526Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition1526Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1526Input0) = fromList transition1526Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1526 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0209 = 1 • support0299 := by
  have hs : support0209 = fromList transition1526Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1526Chunk0]
  have hn : (transition1526Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition1527Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1527Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 640, 642, 644, 646, 705, 707, 709, 711, 512, 514, 516, 518, 577, 579, 581, 583]
private theorem transition1527Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1527Input0) = fromList transition1527Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1527 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0209 = 1 • support0300 := by
  have hs : support0209 = fromList transition1527Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1527Chunk0]
  have hn : (transition1527Raw0 : Multiset ℕ) = 1 • (supportNumbers0300 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0300] using hm

private def transition1528Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1528Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private theorem transition1528Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1528Input0) = fromList transition1528Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1528 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0209 = 1 • support0299 := by
  have hs : support0209 = fromList transition1528Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1528Chunk0]
  have hn : (transition1528Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition1529Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition1529Raw0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197]
private theorem transition1529Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1529Input0) = fromList transition1529Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1529 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0299 = 1 • support1372 := by
  have hs : support0299 = fromList transition1529Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1529Chunk0]
  have hn : (transition1529Raw0 : Multiset ℕ) = 1 • (supportNumbers1372 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1372] using hm

private def transition1530Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199]
private def transition1530Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 128, 706, 132, 710, 193, 643, 197, 647]
private theorem transition1530Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1530Input0) = fromList transition1530Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1530 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0299 = 1 • support1374 := by
  have hs : support0299 = fromList transition1530Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1530Chunk0]
  have hn : (transition1530Raw0 : Multiset ℕ) = 1 • (supportNumbers1374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1374] using hm

private def transition1531Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1531Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743]
private theorem transition1531Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1531Input0) = fromList transition1531Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1531 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0209 = 1 • support1376 := by
  have hs : support0209 = fromList transition1531Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1531Chunk0]
  have hn : (transition1531Raw0 : Multiset ℕ) = 1 • (supportNumbers1376 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1376] using hm

private def transition1532Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition1532Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition1532Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1532Input0) = fromList transition1532Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1532 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1376 = 1 • support0910 := by
  have hs : support1376 = fromList transition1532Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1532Chunk0]
  have hn : (transition1532Raw0 : Multiset ℕ) = 1 • (supportNumbers0910 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0910] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
