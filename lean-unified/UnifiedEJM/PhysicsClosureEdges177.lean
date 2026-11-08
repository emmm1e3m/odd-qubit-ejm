import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3042Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3042Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3042Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3042Input0) = fromList transition3042Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3042Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition3042Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition3042Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3042Input1) = fromList transition3042Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3042 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0454 = 1 • support0090 := by
  have hs : support0454 = fromList transition3042Input0 + fromList transition3042Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3042Chunk0, transition3042Chunk1]
  have hn : (transition3042Raw0 : Multiset ℕ) + (transition3042Raw1 : Multiset ℕ) = 1 • (supportNumbers0090 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0090] using hm

private def transition3043Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3043Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition3043Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3043Input0) = fromList transition3043Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3043Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition3043Raw1 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition3043Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3043Input1) = fromList transition3043Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3043 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0454 = 1 • support0776 := by
  have hs : support0454 = fromList transition3043Input0 + fromList transition3043Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3043Chunk0, transition3043Chunk1]
  have hn : (transition3043Raw0 : Multiset ℕ) + (transition3043Raw1 : Multiset ℕ) = 1 • (supportNumbers0776 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0776] using hm

private def transition3044Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3044Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3044Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3044Input0) = fromList transition3044Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3044Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3044Raw1 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition3044Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3044Input1) = fromList transition3044Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3044 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0455 = 1 • support0411 := by
  have hs : support0455 = fromList transition3044Input0 + fromList transition3044Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3044Chunk0, transition3044Chunk1]
  have hn : (transition3044Raw0 : Multiset ℕ) + (transition3044Raw1 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition3045Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3045Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 728, 729, 730, 731, 732, 733, 734, 735, 520, 521, 522, 523, 524, 525, 526, 527, 144, 145, 146, 147, 148, 149, 150, 151, 584, 585, 586, 587, 588, 589, 590, 591, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3045Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3045Input0) = fromList transition3045Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3045Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3045Raw1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 24, 25, 26, 27, 28, 29, 30, 31, 704, 705, 706, 707, 708, 709, 710, 711, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 528, 529, 530, 531, 532, 533, 534, 535, 200, 201, 202, 203, 204, 205, 206, 207, 592, 593, 594, 595, 596, 597, 598, 599]
private theorem transition3045Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3045Input1) = fromList transition3045Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3045 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0455 = 1 • support0454 := by
  have hs : support0455 = fromList transition3045Input0 + fromList transition3045Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3045Chunk0, transition3045Chunk1]
  have hn : (transition3045Raw0 : Multiset ℕ) + (transition3045Raw1 : Multiset ℕ) = 1 • (supportNumbers0454 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0454] using hm

private def transition3046Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3046Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3046Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3046Input0) = fromList transition3046Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3046Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3046Raw1 : List ℕ := [24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition3046Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3046Input1) = fromList transition3046Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3046 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0455 = 1 • support0411 := by
  have hs : support0455 = fromList transition3046Input0 + fromList transition3046Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3046Chunk0, transition3046Chunk1]
  have hn : (transition3046Raw0 : Multiset ℕ) + (transition3046Raw1 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition3047Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition3047Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 632, 633, 634, 635, 636, 637, 638, 639, 680, 681, 682, 683, 684, 685, 686, 687, 144, 145, 146, 147, 148, 149, 150, 151, 744, 745, 746, 747, 748, 749, 750, 751, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition3047Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3047Input0) = fromList transition3047Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition3047Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition3047Raw1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 24, 25, 26, 27, 28, 29, 30, 31, 608, 609, 610, 611, 612, 613, 614, 615, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 688, 689, 690, 691, 692, 693, 694, 695, 200, 201, 202, 203, 204, 205, 206, 207, 752, 753, 754, 755, 756, 757, 758, 759]
private theorem transition3047Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3047Input1) = fromList transition3047Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3047 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0455 = 1 • support1734 := by
  have hs : support0455 = fromList transition3047Input0 + fromList transition3047Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3047Chunk0, transition3047Chunk1]
  have hn : (transition3047Raw0 : Multiset ℕ) + (transition3047Raw1 : Multiset ℕ) = 1 • (supportNumbers1734 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1734] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
