import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2189Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2189Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 138, 139, 142, 143, 202, 203, 206, 207]
private theorem transition2189Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2189Input0) = fromList transition2189Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2189 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0392 = 1 • support1582 := by
  have hs : support0392 = fromList transition2189Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2189Chunk0]
  have hn : (transition2189Raw0 : Multiset ℕ) = 1 • (supportNumbers1582 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1582] using hm

private def transition2190Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463]
private def transition2190Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 712, 713, 138, 139, 716, 717, 142, 143, 648, 649, 202, 203, 652, 653, 206, 207]
private theorem transition2190Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2190Input0) = fromList transition2190Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2190 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0392 = 1 • support1584 := by
  have hs : support0392 = fromList transition2190Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2190Chunk0]
  have hn : (transition2190Raw0 : Multiset ℕ) = 1 • (supportNumbers1584 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1584] using hm

private def transition2191Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 648, 649, 650, 651, 652, 653, 654, 655, 712, 713, 714, 715, 716, 717, 718, 719]
private def transition2191Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007]
private theorem transition2191Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2191Input0) = fromList transition2191Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2191 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0311 = 1 • support1585 := by
  have hs : support0311 = fromList transition2191Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2191Chunk0]
  have hn : (transition2191Raw0 : Multiset ℕ) = 1 • (supportNumbers1585 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1585] using hm

private def transition2192Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def transition2192Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition2192Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2192Input0) = fromList transition2192Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2192 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1585 = 1 • support0747 := by
  have hs : support1585 = fromList transition2192Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2192Chunk0]
  have hn : (transition2192Raw0 : Multiset ℕ) = 1 • (supportNumbers0747 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0747] using hm

private def transition2193Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 392, 393, 394, 395, 396, 397, 398, 399, 456, 457, 458, 459, 460, 461, 462, 463, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 936, 937, 938, 939, 940, 941, 942, 943, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007]
private def transition2193Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943]
private theorem transition2193Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2193Input0) = fromList transition2193Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2193 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1585 = 1 • support0749 := by
  have hs : support1585 = fromList transition2193Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2193Chunk0]
  have hn : (transition2193Raw0 : Multiset ℕ) = 1 • (supportNumbers0749 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0749] using hm

private def transition2194Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2194Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2194Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2194Input0) = fromList transition2194Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2194 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0312 = 1 • support0222 := by
  have hs : support0312 = fromList transition2194Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2194Chunk0]
  have hn : (transition2194Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition2195Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2195Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 640, 641, 642, 643, 644, 645, 646, 647, 8, 9, 10, 11, 12, 13, 14, 15, 704, 705, 706, 707, 708, 709, 710, 711, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2195Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2195Input0) = fromList transition2195Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2195 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0312 = 1 • support0394 := by
  have hs : support0312 = fromList transition2195Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2195Chunk0]
  have hn : (transition2195Raw0 : Multiset ℕ) = 1 • (supportNumbers0394 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0394] using hm

private def transition2196Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2196Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2196Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2196Input0) = fromList transition2196Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2196 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0312 = 1 • support0222 := by
  have hs : support0312 = fromList transition2196Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2196Chunk0]
  have hn : (transition2196Raw0 : Multiset ℕ) = 1 • (supportNumbers0222 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0222] using hm

private def transition2197Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2197Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623, 544, 545, 546, 547, 548, 549, 550, 551, 8, 9, 10, 11, 12, 13, 14, 15, 608, 609, 610, 611, 612, 613, 614, 615, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2197Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2197Input0) = fromList transition2197Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2197 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0312 = 1 • support1586 := by
  have hs : support0312 = fromList transition2197Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2197Chunk0]
  have hn : (transition2197Raw0 : Multiset ℕ) = 1 • (supportNumbers1586 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1586] using hm

private def transition2198Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]
private def transition2198Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367]
private theorem transition2198Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2198Input0) = fromList transition2198Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2198 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1586 = 1 • support1223 := by
  have hs : support1586 = fromList transition2198Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2198Chunk0]
  have hn : (transition2198Raw0 : Multiset ℕ) = 1 • (supportNumbers1223 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1223] using hm

private def transition2199Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623]
private def transition2199Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815]
private theorem transition2199Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2199Input0) = fromList transition2199Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2199 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1586 = 1 • support1225 := by
  have hs : support1586 = fromList transition2199Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2199Chunk0]
  have hn : (transition2199Raw0 : Multiset ℕ) = 1 • (supportNumbers1225 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1225] using hm

private def transition2200Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2200Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79]
private theorem transition2200Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2200Input0) = fromList transition2200Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2200Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2200Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463]
private theorem transition2200Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2200Input1) = fromList transition2200Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2200 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0313 = 2 • support0328 := by
  have hs : support0313 = fromList transition2200Input0 + fromList transition2200Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2200Chunk0, transition2200Chunk1]
  have hn : (transition2200Raw0 : Multiset ℕ) + (transition2200Raw1 : Multiset ℕ) = 2 • (supportNumbers0328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0328] using hm

private def transition2201Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335]
private def transition2201Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719]
private theorem transition2201Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2201Input0) = fromList transition2201Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2201Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975]
private def transition2201Raw1 : List ℕ := [384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847]
private theorem transition2201Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2201Input1) = fromList transition2201Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2201 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0313 = 2 • support0329 := by
  have hs : support0313 = fromList transition2201Input0 + fromList transition2201Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2201Chunk0, transition2201Chunk1]
  have hn : (transition2201Raw0 : Multiset ℕ) + (transition2201Raw1 : Multiset ℕ) = 2 • (supportNumbers0329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0329] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
