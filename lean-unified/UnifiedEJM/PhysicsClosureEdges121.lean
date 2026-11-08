import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2202Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2202Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2202Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2202Input0) = fromList transition2202Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2202Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2202Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2202Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2202Input1) = fromList transition2202Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2202 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0313 = 2 • support0328 := by
  have hs : support0313 = fromList transition2202Input0 + fromList transition2202Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2202Chunk0, transition2202Chunk1]
  have hn : (transition2202Raw0 : Multiset ℕ) + (transition2202Raw1 : Multiset ℕ) = 2 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2203Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2203Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623]
private theorem transition2203Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2203Input0) = fromList transition2203Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2203Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2203Raw1 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition2203Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2203Input1) = fromList transition2203Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2203 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0313 = 2 • support1445 := by
  have hs : support0313 = fromList transition2203Input0 + fromList transition2203Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2203Chunk0, transition2203Chunk1]
  have hn : (transition2203Raw0 : Multiset ℕ) + (transition2203Raw1 : Multiset ℕ) = 2 • (supportNumbers1445 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1445] using hm

private def transition2204Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2204Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2204Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2204Input0) = fromList transition2204Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2204 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0314 = 1 • support0395 := by
  have hs : support0314 = fromList transition2204Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2204Chunk0]
  have hn : (transition2204Raw0 : Multiset ℕ) = 1 • (supportNumbers0395 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0395] using hm

private def transition2205Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2205Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2205Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2205Input0) = fromList transition2205Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2205 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0314 = 1 • support0396 := by
  have hs : support0314 = fromList transition2205Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2205Chunk0]
  have hn : (transition2205Raw0 : Multiset ℕ) = 1 • (supportNumbers0396 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0396] using hm

private def transition2206Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2206Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2206Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2206Input0) = fromList transition2206Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2206 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0314 = 1 • support0395 := by
  have hs : support0314 = fromList transition2206Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2206Chunk0]
  have hn : (transition2206Raw0 : Multiset ℕ) = 1 • (supportNumbers0395 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0395] using hm

private def transition2207Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2207Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 3, 7, 66, 70, 130, 134, 195, 199]
private theorem transition2207Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2207Input0) = fromList transition2207Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2207 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0395 = 1 • support0908 := by
  have hs : support0395 = fromList transition2207Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2207Chunk0]
  have hn : (transition2207Raw0 : Multiset ℕ) = 1 • (supportNumbers0908 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0908] using hm

private def transition2208Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition2208Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 129, 707, 133, 711, 192, 642, 196, 646, 577, 3, 581, 7, 512, 66, 516, 70, 704, 130, 708, 134, 641, 195, 645, 199]
private theorem transition2208Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2208Input0) = fromList transition2208Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2208 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0395 = 1 • support1587 := by
  have hs : support0395 = fromList transition2208Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2208Chunk0]
  have hn : (transition2208Raw0 : Multiset ℕ) = 1 • (supportNumbers1587 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1587] using hm

private def transition2209Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2209Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2209Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2209Input0) = fromList transition2209Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2209 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0314 = 1 • support1588 := by
  have hs : support0314 = fromList transition2209Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2209Chunk0]
  have hn : (transition2209Raw0 : Multiset ℕ) = 1 • (supportNumbers1588 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1588] using hm

private def transition2210Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 801, 803, 805, 807, 864, 866, 868, 870, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition2210Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 417, 419, 421, 423, 480, 482, 484, 486, 289, 291, 293, 295, 352, 354, 356, 358, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition2210Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2210Input0) = fromList transition2210Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2210 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1588 = 1 • support1204 := by
  have hs : support1588 = fromList transition2210Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2210Chunk0]
  have hn : (transition2210Raw0 : Multiset ℕ) = 1 • (supportNumbers1204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1204] using hm

private def transition2211Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742, 801, 803, 805, 807, 864, 866, 868, 870, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition2211Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 1, 577, 3, 579, 5, 581, 7, 583, 64, 512, 66, 514, 68, 516, 70, 518, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 417, 993, 419, 995, 421, 997, 423, 999, 480, 928, 482, 930, 484, 932, 486, 934, 289, 865, 291, 867, 293, 869, 295, 871, 352, 800, 354, 802, 356, 804, 358, 806, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition2211Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2211Input0) = fromList transition2211Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2211 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1588 = 1 • support1206 := by
  have hs : support1588 = fromList transition2211Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2211Chunk0]
  have hn : (transition2211Raw0 : Multiset ℕ) = 1 • (supportNumbers1206 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1206] using hm

private def transition2212Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2212Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition2212Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2212Input0) = fromList transition2212Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2212 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0315 = 1 • support0144 := by
  have hs : support0315 = fromList transition2212Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2212Chunk0]
  have hn : (transition2212Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition2213Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2213Raw0 : List ℕ := [0, 2, 4, 6, 648, 650, 652, 654, 65, 67, 69, 71, 713, 715, 717, 719, 129, 131, 133, 135, 521, 523, 525, 527, 192, 194, 196, 198, 584, 586, 588, 590]
private theorem transition2213Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2213Input0) = fromList transition2213Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2213 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0315 = 1 • support0397 := by
  have hs : support0315 = fromList transition2213Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2213Chunk0]
  have hn : (transition2213Raw0 : Multiset ℕ) = 1 • (supportNumbers0397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0397] using hm

private def transition2214Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2214Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition2214Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2214Input0) = fromList transition2214Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2214 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0315 = 1 • support0144 := by
  have hs : support0315 = fromList transition2214Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2214Chunk0]
  have hn : (transition2214Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition2215Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2215Raw0 : List ℕ := [0, 2, 4, 6, 552, 554, 556, 558, 65, 67, 69, 71, 617, 619, 621, 623, 129, 131, 133, 135, 681, 683, 685, 687, 192, 194, 196, 198, 744, 746, 748, 750]
private theorem transition2215Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2215Input0) = fromList transition2215Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2215 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0315 = 1 • support1589 := by
  have hs : support0315 = fromList transition2215Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2215Chunk0]
  have hn : (transition2215Raw0 : Multiset ℕ) = 1 • (supportNumbers1589 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1589] using hm

private def transition2216Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 552, 554, 556, 558, 617, 619, 621, 623, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2216Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 296, 298, 300, 302, 361, 363, 365, 367, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2216Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2216Input0) = fromList transition2216Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2216 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1589 = 1 • support1590 := by
  have hs : support1589 = fromList transition2216Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2216Chunk0]
  have hn : (transition2216Raw0 : Multiset ℕ) = 1 • (supportNumbers1590 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1590] using hm

private def transition2217Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 552, 554, 556, 558, 617, 619, 621, 623, 681, 683, 685, 687, 744, 746, 748, 750]
private def transition2217Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 296, 872, 298, 874, 300, 876, 302, 878, 361, 809, 363, 811, 365, 813, 367, 815, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2217Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2217Input0) = fromList transition2217Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2217 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1589 = 1 • support1592 := by
  have hs : support1589 = fromList transition2217Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2217Chunk0]
  have hn : (transition2217Raw0 : Multiset ℕ) = 1 • (supportNumbers1592 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1592] using hm

private def transition2218Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2218Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition2218Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2218Input0) = fromList transition2218Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2218 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0315 = 1 • support0315 := by
  have hs : support0315 = fromList transition2218Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2218Chunk0]
  have hn : (transition2218Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm

private def transition2219Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2219Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 8, 648, 10, 650, 12, 652, 14, 654, 65, 705, 67, 707, 69, 709, 71, 711, 73, 713, 75, 715, 77, 717, 79, 719, 129, 513, 131, 515, 133, 517, 135, 519, 137, 521, 139, 523, 141, 525, 143, 527, 192, 576, 194, 578, 196, 580, 198, 582, 200, 584, 202, 586, 204, 588, 206, 590]
private theorem transition2219Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2219Input0) = fromList transition2219Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2219 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0315 = 1 • support0398 := by
  have hs : support0315 = fromList transition2219Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2219Chunk0]
  have hn : (transition2219Raw0 : Multiset ℕ) = 1 • (supportNumbers0398 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0398] using hm

private def transition2220Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private def transition2220Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem transition2220Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2220Input0) = fromList transition2220Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2220 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0315 = 1 • support0315 := by
  have hs : support0315 = fromList transition2220Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2220Chunk0]
  have hn : (transition2220Raw0 : Multiset ℕ) = 1 • (supportNumbers0315 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0315] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
