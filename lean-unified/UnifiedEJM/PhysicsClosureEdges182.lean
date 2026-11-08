import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition3099Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 512, 514, 516, 518, 577, 579, 581, 583, 640, 642, 644, 646, 705, 707, 709, 711, 777, 779, 781, 783, 840, 842, 844, 846, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition3099Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 9, 553, 11, 555, 13, 557, 15, 559, 72, 616, 74, 618, 76, 620, 78, 622, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition3099Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3099Input0) = fromList transition3099Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3099 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0465 = 1 • support1397 := by
  have hs : support0465 = fromList transition3099Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3099Chunk0]
  have hn : (transition3099Raw0 : Multiset ℕ) = 1 • (supportNumbers1397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1397] using hm

private def transition3100Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition3100Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition3100Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3100Input0) = fromList transition3100Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3100 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0466 = 1 • support0142 := by
  have hs : support0466 = fromList transition3100Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3100Chunk0]
  have hn : (transition3100Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm

private def transition3101Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition3101Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839]
private theorem transition3101Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3101Input0) = fromList transition3101Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3101 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0466 = 1 • support0143 := by
  have hs : support0466 = fromList transition3101Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3101Chunk0]
  have hn : (transition3101Raw0 : Multiset ℕ) = 1 • (supportNumbers0143 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0143] using hm

private def transition3102Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition3102Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 264, 265, 266, 267, 268, 269, 270, 271, 328, 329, 330, 331, 332, 333, 334, 335, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition3102Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3102Input0) = fromList transition3102Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3102 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0466 = 1 • support0142 := by
  have hs : support0466 = fromList transition3102Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3102Chunk0]
  have hn : (transition3102Raw0 : Multiset ℕ) = 1 • (supportNumbers0142 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0142] using hm

private def transition3103Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 520, 521, 522, 523, 524, 525, 526, 527, 584, 585, 586, 587, 588, 589, 590, 591, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711]
private def transition3103Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999]
private theorem transition3103Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3103Input0) = fromList transition3103Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3103 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0466 = 1 • support0946 := by
  have hs : support0466 = fromList transition3103Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3103Chunk0]
  have hn : (transition3103Raw0 : Multiset ℕ) = 1 • (supportNumbers0946 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0946] using hm

private def transition3104Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition3104Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition3104Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3104Input0) = fromList transition3104Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3104 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0467 = 1 • support0144 := by
  have hs : support0467 = fromList transition3104Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3104Chunk0]
  have hn : (transition3104Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition3105Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition3105Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 640, 642, 644, 646, 705, 707, 709, 711, 513, 515, 517, 519, 576, 578, 580, 582]
private theorem transition3105Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3105Input0) = fromList transition3105Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3105 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0467 = 1 • support0314 := by
  have hs : support0467 = fromList transition3105Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3105Chunk0]
  have hn : (transition3105Raw0 : Multiset ℕ) = 1 • (supportNumbers0314 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0314] using hm

private def transition3106Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition3106Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198]
private theorem transition3106Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3106Input0) = fromList transition3106Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3106 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0467 = 1 • support0144 := by
  have hs : support0467 = fromList transition3106Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3106Chunk0]
  have hn : (transition3106Raw0 : Multiset ℕ) = 1 • (supportNumbers0144 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0144] using hm

private def transition3107Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454]
private def transition3107Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 544, 546, 548, 550, 609, 611, 613, 615, 673, 675, 677, 679, 736, 738, 740, 742]
private theorem transition3107Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3107Input0) = fromList transition3107Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3107 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0467 = 1 • support1407 := by
  have hs : support0467 = fromList transition3107Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3107Chunk0]
  have hn : (transition3107Raw0 : Multiset ℕ) = 1 • (supportNumbers1407 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1407] using hm

private def transition3108Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition3108Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition3108Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3108Input0) = fromList transition3108Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3108 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0468 = 2 • support0395 := by
  have hs : support0468 = fromList transition3108Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3108Chunk0]
  have hn : (transition3108Raw0 : Multiset ℕ) = 2 • (supportNumbers0395 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0395] using hm

private def transition3109Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition3109Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 129, 513, 131, 515, 133, 517, 135, 519, 192, 576, 194, 578, 196, 580, 198, 582, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 257, 897, 259, 899, 261, 901, 263, 903, 320, 960, 322, 962, 324, 964, 326, 966, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition3109Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3109Input0) = fromList transition3109Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3109 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0468 = 2 • support0396 := by
  have hs : support0468 = fromList transition3109Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3109Chunk0]
  have hn : (transition3109Raw0 : Multiset ℕ) = 2 • (supportNumbers0396 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0396] using hm

private def transition3110Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition3110Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455, 257, 259, 261, 263, 320, 322, 324, 326, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition3110Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3110Input0) = fromList transition3110Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3110 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0468 = 2 • support0395 := by
  have hs : support0468 = fromList transition3110Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3110Chunk0]
  have hn : (transition3110Raw0 : Multiset ℕ) = 2 • (supportNumbers0395 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0395] using hm

private def transition3111Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 256, 258, 260, 262, 321, 323, 325, 327, 385, 387, 389, 391, 448, 450, 452, 454, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 769, 771, 773, 775, 832, 834, 836, 838, 896, 898, 900, 902, 961, 963, 965, 967]
private def transition3111Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 129, 673, 131, 675, 133, 677, 135, 679, 192, 736, 194, 738, 196, 740, 198, 742, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 257, 801, 259, 803, 261, 805, 263, 807, 320, 864, 322, 866, 324, 868, 326, 870, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition3111Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition3111Input0) = fromList transition3111Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3111 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0468 = 2 • support1588 := by
  have hs : support0468 = fromList transition3111Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3111Chunk0]
  have hn : (transition3111Raw0 : Multiset ℕ) = 2 • (supportNumbers1588 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1588] using hm

private def transition3112Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition3112Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition3112Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition3112Input0) = fromList transition3112Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3112 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0082 = 1 • support0082 := by
  have hs : support0082 = fromList transition3112Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3112Chunk0]
  have hn : (transition3112Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm

private def transition3113Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition3113Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 9, 649, 11, 651, 13, 653, 15, 655, 65, 705, 67, 707, 69, 709, 71, 711, 72, 712, 74, 714, 76, 716, 78, 718, 129, 513, 131, 515, 133, 517, 135, 519, 136, 520, 138, 522, 140, 524, 142, 526, 192, 576, 194, 578, 196, 580, 198, 582, 201, 585, 203, 587, 205, 589, 207, 591]
private theorem transition3113Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition3113Input0) = fromList transition3113Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3113 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0082 = 1 • support0226 := by
  have hs : support0082 = fromList transition3113Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3113Chunk0]
  have hn : (transition3113Raw0 : Multiset ℕ) = 1 • (supportNumbers0226 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0226] using hm

private def transition3114Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def transition3114Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private theorem transition3114Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition3114Input0) = fromList transition3114Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition3114 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0082 = 1 • support0082 := by
  have hs : support0082 = fromList transition3114Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition3114Chunk0]
  have hn : (transition3114Raw0 : Multiset ℕ) = 1 • (supportNumbers0082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0082] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
