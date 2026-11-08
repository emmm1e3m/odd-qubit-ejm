import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1787Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1787Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93]
private theorem transition1787Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1787Input0) = fromList transition1787Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1787Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition1787Raw1 : List ℕ := [2, 3, 6, 7, 10, 11, 14, 15, 18, 19, 22, 23, 26, 27, 30, 31, 66, 67, 70, 71, 74, 75, 78, 79, 82, 83, 86, 87, 90, 91, 94, 95]
private theorem transition1787Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1787Input1) = fromList transition1787Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1787 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0341 = 1 • support0246 := by
  have hs : support0341 = fromList transition1787Input0 + fromList transition1787Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1787Chunk0, transition1787Chunk1]
  have hn : (transition1787Raw0 : Multiset ℕ) + (transition1787Raw1 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm

private def transition1788Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1788Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 8, 9, 586, 587, 12, 13, 590, 591, 16, 17, 594, 595, 20, 21, 598, 599, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 72, 73, 522, 523, 76, 77, 526, 527, 80, 81, 530, 531, 84, 85, 534, 535, 88, 89, 538, 539, 92, 93, 542, 543]
private theorem transition1788Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1788Input0) = fromList transition1788Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1788Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition1788Raw1 : List ℕ := [576, 577, 2, 3, 580, 581, 6, 7, 584, 585, 10, 11, 588, 589, 14, 15, 592, 593, 18, 19, 596, 597, 22, 23, 600, 601, 26, 27, 604, 605, 30, 31, 512, 513, 66, 67, 516, 517, 70, 71, 520, 521, 74, 75, 524, 525, 78, 79, 528, 529, 82, 83, 532, 533, 86, 87, 536, 537, 90, 91, 540, 541, 94, 95]
private theorem transition1788Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1788Input1) = fromList transition1788Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1788 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0341 = 1 • support0247 := by
  have hs : support0341 = fromList transition1788Input0 + fromList transition1788Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1788Chunk0, transition1788Chunk1]
  have hn : (transition1788Raw0 : Multiset ℕ) + (transition1788Raw1 : Multiset ℕ) = 1 • (supportNumbers0247 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0247] using hm

private def transition1789Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1789Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 8, 552, 9, 553, 10, 554, 11, 555, 12, 556, 13, 557, 14, 558, 15, 559, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 72, 616, 73, 617, 74, 618, 75, 619, 76, 620, 77, 621, 78, 622, 79, 623, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639]
private theorem transition1789Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1789Input0) = fromList transition1789Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1789Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607]
private def transition1789Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition1789Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1789Input1) = fromList transition1789Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1789 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0247 = 1 • support1474 := by
  have hs : support0247 = fromList transition1789Input0 + fromList transition1789Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1789Chunk0, transition1789Chunk1]
  have hn : (transition1789Raw0 : Multiset ℕ) + (transition1789Raw1 : Multiset ℕ) = 1 • (supportNumbers1474 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1474] using hm

private def transition1790Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1790Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1790Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1790Input0) = fromList transition1790Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1790Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition1790Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1790Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1790Input1) = fromList transition1790Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1790Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition1790Raw2 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]
private theorem transition1790Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1790Input2) = fromList transition1790Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1790Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]
private def transition1790Raw3 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383]
private theorem transition1790Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1790Input3) = fromList transition1790Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1790 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1474 = 2 • support1001 := by
  have hs : support1474 = fromList transition1790Input0 + fromList transition1790Input1 + fromList transition1790Input2 + fromList transition1790Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1790Chunk0, transition1790Chunk1, transition1790Chunk2, transition1790Chunk3]
  have hn : (transition1790Raw0 : Multiset ℕ) + (transition1790Raw1 : Multiset ℕ) + (transition1790Raw2 : Multiset ℕ) + (transition1790Raw3 : Multiset ℕ) = 2 • (supportNumbers1001 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1001] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
