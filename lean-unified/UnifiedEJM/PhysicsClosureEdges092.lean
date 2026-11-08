import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1674Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839]
private def transition1674Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327]
private theorem transition1674Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1674Input0) = fromList transition1674Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1674 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0232 = 1 • support0320 := by
  have hs : support0232 = fromList transition1674Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1674Chunk0]
  have hn : (transition1674Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition1675Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839]
private def transition1675Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967]
private theorem transition1675Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1675Input0) = fromList transition1675Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1675 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0232 = 1 • support0321 := by
  have hs : support0232 = fromList transition1675Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1675Chunk0]
  have hn : (transition1675Raw0 : Multiset ℕ) = 1 • (supportNumbers0321 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0321] using hm

private def transition1676Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839]
private def transition1676Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327]
private theorem transition1676Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1676Input0) = fromList transition1676Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1676 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0232 = 1 • support0320 := by
  have hs : support0232 = fromList transition1676Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1676Chunk0]
  have hn : (transition1676Raw0 : Multiset ℕ) = 1 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition1677Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1677Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 128, 129, 132, 133, 192, 193, 196, 197, 2, 3, 6, 7, 66, 67, 70, 71, 130, 131, 134, 135, 194, 195, 198, 199]
private theorem transition1677Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1677Input0) = fromList transition1677Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1677 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0320 = 1 • support0229 := by
  have hs : support0320 = fromList transition1677Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1677Chunk0]
  have hn : (transition1677Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition1678Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1678Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 128, 129, 706, 707, 132, 133, 710, 711, 192, 193, 642, 643, 196, 197, 646, 647, 576, 577, 2, 3, 580, 581, 6, 7, 512, 513, 66, 67, 516, 517, 70, 71, 704, 705, 130, 131, 708, 709, 134, 135, 640, 641, 194, 195, 644, 645, 198, 199]
private theorem transition1678Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1678Input0) = fromList transition1678Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1678 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0320 = 1 • support0401 := by
  have hs : support0320 = fromList transition1678Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1678Chunk0]
  have hn : (transition1678Raw0 : Multiset ℕ) = 1 • (supportNumbers0401 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0401] using hm

private def transition1679Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839]
private def transition1679Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871]
private theorem transition1679Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1679Input0) = fromList transition1679Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1679 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0232 = 1 • support1427 := by
  have hs : support0232 = fromList transition1679Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1679Chunk0]
  have hn : (transition1679Raw0 : Multiset ℕ) = 1 • (supportNumbers1427 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1427] using hm

private def transition1680Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1680Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition1680Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1680Input0) = fromList transition1680Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1680Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition1680Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition1680Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1680Input1) = fromList transition1680Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1680 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1427 = 2 • support1204 := by
  have hs : support1427 = fromList transition1680Input0 + fromList transition1680Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1680Chunk0, transition1680Chunk1]
  have hn : (transition1680Raw0 : Multiset ℕ) + (transition1680Raw1 : Multiset ℕ) = 2 • (supportNumbers1204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1204] using hm

private def transition1681Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition1681Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647]
private theorem transition1681Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1681Input0) = fromList transition1681Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1681Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743, 800, 801, 802, 803, 804, 805, 806, 807, 864, 865, 866, 867, 868, 869, 870, 871, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition1681Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition1681Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1681Input1) = fromList transition1681Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1681 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1427 = 2 • support1206 := by
  have hs : support1427 = fromList transition1681Input0 + fromList transition1681Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1681Chunk0, transition1681Chunk1]
  have hn : (transition1681Raw0 : Multiset ℕ) + (transition1681Raw1 : Multiset ℕ) = 2 • (supportNumbers1206 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1206] using hm

private def transition1682Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition1682Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition1682Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1682Input0) = fromList transition1682Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1682 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0233 = 1 • support0322 := by
  have hs : support0233 = fromList transition1682Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1682Chunk0]
  have hn : (transition1682Raw0 : Multiset ℕ) = 1 • (supportNumbers0322 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0322] using hm

private def transition1683Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition1683Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991]
private theorem transition1683Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1683Input0) = fromList transition1683Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1683 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0233 = 1 • support0323 := by
  have hs : support0233 = fromList transition1683Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1683Chunk0]
  have hn : (transition1683Raw0 : Multiset ℕ) = 1 • (supportNumbers0323 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0323] using hm

private def transition1684Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition1684Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition1684Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1684Input0) = fromList transition1684Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1684 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0233 = 1 • support0322 := by
  have hs : support0233 = fromList transition1684Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1684Chunk0]
  have hn : (transition1684Raw0 : Multiset ℕ) = 1 • (supportNumbers0322 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0322] using hm

private def transition1685Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition1685Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 26, 27, 30, 31, 90, 91, 94, 95]
private theorem transition1685Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1685Input0) = fromList transition1685Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1685 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0322 = 1 • support1428 := by
  have hs : support0322 = fromList transition1685Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1685Chunk0]
  have hn : (transition1685Raw0 : Multiset ℕ) = 1 • (supportNumbers1428 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1428] using hm

private def transition1686Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition1686Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 600, 601, 26, 27, 604, 605, 30, 31, 536, 537, 90, 91, 540, 541, 94, 95]
private theorem transition1686Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1686Input0) = fromList transition1686Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1686 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0322 = 1 • support1430 := by
  have hs : support0322 = fromList transition1686Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1686Chunk0]
  have hn : (transition1686Raw0 : Multiset ℕ) = 1 • (supportNumbers1430 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1430] using hm

private def transition1687Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 536, 537, 538, 539, 540, 541, 542, 543, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition1687Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition1687Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1687Input0) = fromList transition1687Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1687 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0233 = 1 • support1431 := by
  have hs : support0233 = fromList transition1687Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1687Chunk0]
  have hn : (transition1687Raw0 : Multiset ℕ) = 1 • (supportNumbers1431 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1431] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
