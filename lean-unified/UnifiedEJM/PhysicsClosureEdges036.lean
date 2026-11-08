import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0650Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719]
private def transition0650Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition0650Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0650Input0) = fromList transition0650Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0650 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0083 = 1 • support0146 := by
  have hs : support0083 = fromList transition0650Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0650Chunk0]
  have hn : (transition0650Raw0 : Multiset ℕ) = 1 • (supportNumbers0146 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0146] using hm

private def transition0651Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition0651Raw0 : List ℕ := [0, 4, 9, 13, 65, 69, 72, 76, 129, 133, 136, 140, 192, 196, 201, 205, 2, 6, 11, 15, 67, 71, 74, 78, 131, 135, 138, 142, 194, 198, 203, 207]
private theorem transition0651Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0651Input0) = fromList transition0651Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0651 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0146 = 1 • support0082 := by
  have hs : support0146 = fromList transition0651Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0651Chunk0]
  have hn : (transition0651Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition0652Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition0652Raw0 : List ℕ := [0, 578, 4, 582, 9, 587, 13, 591, 65, 515, 69, 519, 72, 522, 76, 526, 129, 707, 133, 711, 136, 714, 140, 718, 192, 642, 196, 646, 201, 651, 205, 655, 576, 2, 580, 6, 585, 11, 589, 15, 513, 67, 517, 71, 520, 74, 524, 78, 705, 131, 709, 135, 712, 138, 716, 142, 640, 194, 644, 198, 649, 203, 653, 207]
private theorem transition0652Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0652Input0) = fromList transition0652Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0652 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0146 = 1 • support0226 := by
  have hs : support0146 = fromList transition0652Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0652Chunk0]
  have hn : (transition0652Raw0 : Multiset ℕ) = 1 • (supportNumbers0226 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0226] using hm

private def transition0653Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719]
private def transition0653Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 9, 553, 11, 555, 13, 557, 15, 559, 65, 609, 67, 611, 69, 613, 71, 615, 72, 616, 74, 618, 76, 620, 78, 622, 129, 673, 131, 675, 133, 677, 135, 679, 136, 680, 138, 682, 140, 684, 142, 686, 192, 736, 194, 738, 196, 740, 198, 742, 201, 745, 203, 747, 205, 749, 207, 751, 256, 800, 258, 802, 260, 804, 262, 806, 265, 809, 267, 811, 269, 813, 271, 815, 321, 865, 323, 867, 325, 869, 327, 871, 328, 872, 330, 874, 332, 876, 334, 878, 385, 929, 387, 931, 389, 933, 391, 935, 392, 936, 394, 938, 396, 940, 398, 942, 448, 992, 450, 994, 452, 996, 454, 998, 457, 1001, 459, 1003, 461, 1005, 463, 1007]
private theorem transition0653Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0653Input0) = fromList transition0653Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0653 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0083 = 1 • support0956 := by
  have hs : support0083 = fromList transition0653Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0653Chunk0]
  have hn : (transition0653Raw0 : Multiset ℕ) = 1 • (supportNumbers0956 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0956] using hm

private def transition0654Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition0654Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition0654Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0654Input0) = fromList transition0654Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0654Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878, 929, 931, 933, 935, 936, 938, 940, 942, 992, 994, 996, 998, 1001, 1003, 1005, 1007]
private def transition0654Raw1 : List ℕ := [288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private theorem transition0654Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0654Input1) = fromList transition0654Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0654 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0956 = 2 • support0957 := by
  have hs : support0956 = fromList transition0654Input0 + fromList transition0654Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0654Chunk0, transition0654Chunk1]
  have hn : (transition0654Raw0 : Multiset ℕ) + (transition0654Raw1 : Multiset ℕ) = 2 • (supportNumbers0957 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0957] using hm

private def transition0655Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private def transition0655Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655, 0, 576, 2, 578, 4, 580, 6, 582, 9, 585, 11, 587, 13, 589, 15, 591, 65, 513, 67, 515, 69, 517, 71, 519, 72, 520, 74, 522, 76, 524, 78, 526, 129, 705, 131, 707, 133, 709, 135, 711, 136, 712, 138, 714, 140, 716, 142, 718, 192, 640, 194, 642, 196, 644, 198, 646, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition0655Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0655Input0) = fromList transition0655Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0655Input1 : List ℕ := [544, 546, 548, 550, 553, 555, 557, 559, 609, 611, 613, 615, 616, 618, 620, 622, 673, 675, 677, 679, 680, 682, 684, 686, 736, 738, 740, 742, 745, 747, 749, 751, 800, 802, 804, 806, 809, 811, 813, 815, 865, 867, 869, 871, 872, 874, 876, 878, 929, 931, 933, 935, 936, 938, 940, 942, 992, 994, 996, 998, 1001, 1003, 1005, 1007]
private def transition0655Raw1 : List ℕ := [288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 417, 993, 419, 995, 421, 997, 423, 999, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 480, 928, 482, 930, 484, 932, 486, 934, 489, 937, 491, 939, 493, 941, 495, 943, 288, 864, 290, 866, 292, 868, 294, 870, 297, 873, 299, 875, 301, 877, 303, 879, 353, 801, 355, 803, 357, 805, 359, 807, 360, 808, 362, 810, 364, 812, 366, 814, 417, 993, 419, 995, 421, 997, 423, 999, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 480, 928, 482, 930, 484, 932, 486, 934, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0655Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0655Input1) = fromList transition0655Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0655 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0956 = 2 • support0959 := by
  have hs : support0956 = fromList transition0655Input0 + fromList transition0655Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0655Chunk0, transition0655Chunk1]
  have hn : (transition0655Raw0 : Multiset ℕ) + (transition0655Raw1 : Multiset ℕ) = 2 • (supportNumbers0959 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0959] using hm

private def transition0656Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0656Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition0656Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0656Input0) = fromList transition0656Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0656Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition0656Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition0656Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0656Input1) = fromList transition0656Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0656 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0084 = 1 • support0148 := by
  have hs : support0084 = fromList transition0656Input0 + fromList transition0656Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0656Chunk0, transition0656Chunk1]
  have hn : (transition0656Raw0 : Multiset ℕ) + (transition0656Raw1 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def transition0657Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0657Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 128, 129, 130, 131, 132, 133, 134, 135, 520, 521, 522, 523, 524, 525, 526, 527, 192, 193, 194, 195, 196, 197, 198, 199, 584, 585, 586, 587, 588, 589, 590, 591]
private theorem transition0657Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0657Input0) = fromList transition0657Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0657Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition0657Raw1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 8, 9, 10, 11, 12, 13, 14, 15, 704, 705, 706, 707, 708, 709, 710, 711, 72, 73, 74, 75, 76, 77, 78, 79, 512, 513, 514, 515, 516, 517, 518, 519, 136, 137, 138, 139, 140, 141, 142, 143, 576, 577, 578, 579, 580, 581, 582, 583, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition0657Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0657Input1) = fromList transition0657Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0657 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0084 = 1 • support0149 := by
  have hs : support0084 = fromList transition0657Input0 + fromList transition0657Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0657Chunk0, transition0657Chunk1]
  have hn : (transition0657Raw0 : Multiset ℕ) + (transition0657Raw1 : Multiset ℕ) = 1 • (supportNumbers0149 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0149] using hm

private def transition0658Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0658Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition0658Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0658Input0) = fromList transition0658Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0658Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition0658Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition0658Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0658Input1) = fromList transition0658Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0658 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0084 = 1 • support0148 := by
  have hs : support0084 = fromList transition0658Input0 + fromList transition0658Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0658Chunk0, transition0658Chunk1]
  have hn : (transition0658Raw0 : Multiset ℕ) + (transition0658Raw1 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def transition0659Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0659Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 128, 129, 132, 133, 136, 137, 140, 141, 192, 193, 196, 197, 200, 201, 204, 205]
private theorem transition0659Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0659Input0) = fromList transition0659Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0659 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0148 = 1 • support0960 := by
  have hs : support0148 = fromList transition0659Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0659Chunk0]
  have hn : (transition0659Raw0 : Multiset ℕ) = 1 • (supportNumbers0960 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0960] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
