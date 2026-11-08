import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0634Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition0634Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 1, 3, 5, 7, 64, 66, 68, 70, 136, 138, 140, 142, 201, 203, 205, 207, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335, 385, 387, 389, 391, 448, 450, 452, 454]
private theorem transition0634Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0634Input0) = fromList transition0634Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0634 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0081 = 1 • support0142 := by
  have hs : support0081 = fromList transition0634Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0634Chunk0]
  have hn : (transition0634Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm

private def transition0635Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0635Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205, 10, 11, 14, 15, 74, 75, 78, 79, 130, 131, 134, 135, 194, 195, 198, 199]
private theorem transition0635Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0635Input0) = fromList transition0635Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0635 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0142 = 1 • support0943 := by
  have hs : support0142 = fromList transition0635Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0635Chunk0]
  have hn : (transition0635Raw0 : Multiset ℕ) = 1 • (supportNumbers0943 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0943] using hm

private def transition0636Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0636Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 136, 137, 714, 715, 140, 141, 718, 719, 200, 201, 650, 651, 204, 205, 654, 655, 584, 585, 10, 11, 588, 589, 14, 15, 520, 521, 74, 75, 524, 525, 78, 79, 704, 705, 130, 131, 708, 709, 134, 135, 640, 641, 194, 195, 644, 645, 198, 199]
private theorem transition0636Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0636Input0) = fromList transition0636Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0636 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0142 = 1 • support0945 := by
  have hs : support0142 = fromList transition0636Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0636Chunk0]
  have hn : (transition0636Raw0 : Multiset ℕ) = 1 • (supportNumbers0945 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0945] using hm

private def transition0637Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 257, 259, 261, 263, 320, 322, 324, 326, 392, 394, 396, 398, 457, 459, 461, 463, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847, 897, 899, 901, 903, 960, 962, 964, 966]
private def transition0637Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 1, 545, 3, 547, 5, 549, 7, 551, 64, 608, 66, 610, 68, 612, 70, 614, 136, 680, 138, 682, 140, 684, 142, 686, 201, 745, 203, 747, 205, 749, 207, 751, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879, 385, 929, 387, 931, 389, 933, 391, 935, 448, 992, 450, 994, 452, 996, 454, 998]
private theorem transition0637Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0637Input0) = fromList transition0637Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0637 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0081 = 1 • support0946 := by
  have hs : support0081 = fromList transition0637Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0637Chunk0]
  have hn : (transition0637Raw0 : Multiset ℕ) = 1 • (supportNumbers0946 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0946] using hm

private def transition0638Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0638Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition0638Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0638Input0) = fromList transition0638Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0638Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition0638Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 296, 297, 298, 299, 300, 301, 302, 303, 360, 361, 362, 363, 364, 365, 366, 367, 416, 417, 418, 419, 420, 421, 422, 423, 480, 481, 482, 483, 484, 485, 486, 487]
private theorem transition0638Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0638Input1) = fromList transition0638Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0638 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0946 = 1 • support0616 := by
  have hs : support0946 = fromList transition0638Input0 + fromList transition0638Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0638Chunk0, transition0638Chunk1]
  have hn : (transition0638Raw0 : Multiset ℕ) + (transition0638Raw1 : Multiset ℕ) = 1 • (supportNumbers0616 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0616] using hm

private def transition0639Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition0639Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 8, 584, 9, 585, 10, 586, 11, 587, 12, 588, 13, 589, 14, 590, 15, 591, 72, 520, 73, 521, 74, 522, 75, 523, 76, 524, 77, 525, 78, 526, 79, 527, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647]
private theorem transition0639Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0639Input0) = fromList transition0639Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0639Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 808, 809, 810, 811, 812, 813, 814, 815, 872, 873, 874, 875, 876, 877, 878, 879, 928, 929, 930, 931, 932, 933, 934, 935, 992, 993, 994, 995, 996, 997, 998, 999]
private def transition0639Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935]
private theorem transition0639Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0639Input1) = fromList transition0639Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0639 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0946 = 1 • support0618 := by
  have hs : support0946 = fromList transition0639Input0 + fromList transition0639Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0639Chunk0, transition0639Chunk1]
  have hn : (transition0639Raw0 : Multiset ℕ) + (transition0639Raw1 : Multiset ℕ) = 1 • (supportNumbers0618 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0618] using hm

private def transition0640Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0640Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition0640Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0640Input0) = fromList transition0640Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0640 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0082 = 1 • support0144 := by
  have hs : support0082 = fromList transition0640Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0640Chunk0]
  have hn : (transition0640Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition0641Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0641Raw0 : List ℕ := [0, 2, 4, 6, 649, 651, 653, 655, 65, 67, 69, 71, 712, 714, 716, 718, 129, 131, 133, 135, 520, 522, 524, 526, 192, 194, 196, 198, 585, 587, 589, 591]
private theorem transition0641Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0641Input0) = fromList transition0641Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0641 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0082 = 1 • support0145 := by
  have hs : support0082 = fromList transition0641Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0641Chunk0]
  have hn : (transition0641Raw0 : Multiset ℕ) = 1 • (supportNumbers0145 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0145] using hm

private def transition0642Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0642Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition0642Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0642Input0) = fromList transition0642Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0642 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0082 = 1 • support0144 := by
  have hs : support0082 = fromList transition0642Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0642Chunk0]
  have hn : (transition0642Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition0643Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition0643Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196]
private theorem transition0643Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0643Input0) = fromList transition0643Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0643 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0144 = 1 • support0947 := by
  have hs : support0144 = fromList transition0643Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0643Chunk0]
  have hn : (transition0643Raw0 : Multiset ℕ) = 1 • (supportNumbers0947 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0947] using hm

private def transition0644Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private def transition0644Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 129, 707, 133, 711, 192, 642, 196, 646]
private theorem transition0644Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0644Input0) = fromList transition0644Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0644 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0144 = 1 • support0949 := by
  have hs : support0144 = fromList transition0644Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0644Chunk0]
  have hn : (transition0644Raw0 : Multiset ℕ) = 1 • (supportNumbers0949 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0949] using hm

private def transition0645Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition0645Raw0 : List ℕ := [0, 2, 4, 6, 553, 555, 557, 559, 65, 67, 69, 71, 616, 618, 620, 622, 129, 131, 133, 135, 680, 682, 684, 686, 192, 194, 196, 198, 745, 747, 749, 751]
private theorem transition0645Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0645Input0) = fromList transition0645Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0645 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0082 = 1 • support0950 := by
  have hs : support0082 = fromList transition0645Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0645Chunk0]
  have hn : (transition0645Raw0 : Multiset ℕ) = 1 • (supportNumbers0950 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0950] using hm

private def transition0646Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 553, 555, 557, 559, 616, 618, 620, 622, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0646Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 297, 299, 301, 303, 360, 362, 364, 366, 424, 426, 428, 430, 489, 491, 493, 495]
private theorem transition0646Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0646Input0) = fromList transition0646Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0646 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0950 = 1 • support0951 := by
  have hs : support0950 = fromList transition0646Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0646Chunk0]
  have hn : (transition0646Raw0 : Multiset ℕ) = 1 • (supportNumbers0951 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0951] using hm

private def transition0647Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 553, 555, 557, 559, 616, 618, 620, 622, 680, 682, 684, 686, 745, 747, 749, 751]
private def transition0647Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 129, 705, 131, 707, 133, 709, 135, 711, 192, 640, 194, 642, 196, 644, 198, 646, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 424, 1000, 426, 1002, 428, 1004, 430, 1006, 489, 937, 491, 939, 493, 941, 495, 943]
private theorem transition0647Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0647Input0) = fromList transition0647Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0647 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0950 = 1 • support0953 := by
  have hs : support0950 = fromList transition0647Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0647Chunk0]
  have hn : (transition0647Raw0 : Multiset ℕ) = 1 • (supportNumbers0953 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0953] using hm

private def transition0648Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719]
private def transition0648Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 256, 258, 260, 262, 265, 267, 269, 271, 321, 323, 325, 327, 328, 330, 332, 334, 385, 387, 389, 391, 392, 394, 396, 398, 448, 450, 452, 454, 457, 459, 461, 463]
private theorem transition0648Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0648Input0) = fromList transition0648Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0648 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0083 = 1 • support0146 := by
  have hs : support0083 = fromList transition0648Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0648Chunk0]
  have hn : (transition0648Raw0 : Multiset ℕ) = 1 • (supportNumbers0146 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0146] using hm

private def transition0649Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 512, 514, 516, 518, 521, 523, 525, 527, 577, 579, 581, 583, 584, 586, 588, 590, 641, 643, 645, 647, 648, 650, 652, 654, 704, 706, 708, 710, 713, 715, 717, 719]
private def transition0649Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591, 256, 896, 258, 898, 260, 900, 262, 902, 265, 905, 267, 907, 269, 909, 271, 911, 321, 961, 323, 963, 325, 965, 327, 967, 328, 968, 330, 970, 332, 972, 334, 974, 385, 769, 387, 771, 389, 773, 391, 775, 392, 776, 394, 778, 396, 780, 398, 782, 448, 832, 450, 834, 452, 836, 454, 838, 457, 841, 459, 843, 461, 845, 463, 847]
private theorem transition0649Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0649Input0) = fromList transition0649Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0649 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0083 = 1 • support0147 := by
  have hs : support0083 = fromList transition0649Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0649Chunk0]
  have hn : (transition0649Raw0 : Multiset ℕ) = 1 • (supportNumbers0147 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0147] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
