import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0698Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0698Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0698Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0698Input0) = fromList transition0698Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0698 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0089 = 1 • support0155 := by
  have hs : support0089 = fromList transition0698Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0698Chunk0]
  have hn : (transition0698Raw0 : Multiset ℕ) = 1 • (supportNumbers0155 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0155] using hm

private def transition0699Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0699Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205, 18, 19, 22, 23, 82, 83, 86, 87, 154, 155, 158, 159, 218, 219, 222, 223]
private theorem transition0699Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0699Input0) = fromList transition0699Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0699 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0155 = 1 • support0984 := by
  have hs : support0155 = fromList transition0699Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0699Chunk0]
  have hn : (transition0699Raw0 : Multiset ℕ) = 1 • (supportNumbers0984 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0984] using hm

private def transition0700Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0700Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 136, 137, 714, 715, 140, 141, 718, 719, 200, 201, 650, 651, 204, 205, 654, 655, 592, 593, 18, 19, 596, 597, 22, 23, 528, 529, 82, 83, 532, 533, 86, 87, 728, 729, 154, 155, 732, 733, 158, 159, 664, 665, 218, 219, 668, 669, 222, 223]
private theorem transition0700Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0700Input0) = fromList transition0700Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0700 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0155 = 1 • support0986 := by
  have hs : support0155 = fromList transition0700Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0700Chunk0]
  have hn : (transition0700Raw0 : Multiset ℕ) = 1 • (supportNumbers0986 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0986] using hm

private def transition0701Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 528, 529, 530, 531, 532, 533, 534, 535, 592, 593, 594, 595, 596, 597, 598, 599, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0701Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0701Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0701Input0) = fromList transition0701Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0701 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0089 = 1 • support0987 := by
  have hs : support0089 = fromList transition0701Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0701Chunk0]
  have hn : (transition0701Raw0 : Multiset ℕ) = 1 • (supportNumbers0987 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0987] using hm

private def transition0702Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0702Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 16, 17, 18, 19, 20, 21, 22, 23, 80, 81, 82, 83, 84, 85, 86, 87, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0702Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0702Input0) = fromList transition0702Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0702Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 816, 817, 818, 819, 820, 821, 822, 823, 880, 881, 882, 883, 884, 885, 886, 887, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0702Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495, 304, 305, 306, 307, 308, 309, 310, 311, 368, 369, 370, 371, 372, 373, 374, 375, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition0702Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0702Input1) = fromList transition0702Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0702 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0987 = 1 • support0787 := by
  have hs : support0987 = fromList transition0702Input0 + fromList transition0702Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0702Chunk0, transition0702Chunk1]
  have hn : (transition0702Raw0 : Multiset ℕ) + (transition0702Raw1 : Multiset ℕ) = 1 • (supportNumbers0787 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0787] using hm

private def transition0703Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 272, 273, 274, 275, 276, 277, 278, 279, 336, 337, 338, 339, 340, 341, 342, 343, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0703Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671]
private theorem transition0703Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0703Input0) = fromList transition0703Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0703Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751, 816, 817, 818, 819, 820, 821, 822, 823, 880, 881, 882, 883, 884, 885, 886, 887, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0703Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 428, 1004, 429, 1005, 430, 1006, 431, 1007, 488, 936, 489, 937, 490, 938, 491, 939, 492, 940, 493, 941, 494, 942, 495, 943, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0703Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0703Input1) = fromList transition0703Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0703 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0987 = 1 • support0789 := by
  have hs : support0987 = fromList transition0703Input0 + fromList transition0703Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0703Chunk0, transition0703Chunk1]
  have hn : (transition0703Raw0 : Multiset ℕ) + (transition0703Raw1 : Multiset ℕ) = 1 • (supportNumbers0789 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0789] using hm

private def transition0704Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition0704Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0704Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0704Input0) = fromList transition0704Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0704Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0704Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0704Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0704Input1) = fromList transition0704Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0704 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0090 = 1 • support0157 := by
  have hs : support0090 = fromList transition0704Input0 + fromList transition0704Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0704Chunk0, transition0704Chunk1]
  have hn : (transition0704Raw0 : Multiset ℕ) + (transition0704Raw1 : Multiset ℕ) = 1 • (supportNumbers0157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0157] using hm

private def transition0705Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition0705Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 728, 729, 730, 731, 732, 733, 734, 735, 520, 521, 522, 523, 524, 525, 526, 527, 144, 145, 146, 147, 148, 149, 150, 151, 584, 585, 586, 587, 588, 589, 590, 591, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0705Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0705Input0) = fromList transition0705Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0705Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0705Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 656, 657, 658, 659, 660, 661, 662, 663, 72, 73, 74, 75, 76, 77, 78, 79, 720, 721, 722, 723, 724, 725, 726, 727, 512, 513, 514, 515, 516, 517, 518, 519, 152, 153, 154, 155, 156, 157, 158, 159, 576, 577, 578, 579, 580, 581, 582, 583, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0705Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0705Input1) = fromList transition0705Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0705 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0090 = 1 • support0158 := by
  have hs : support0090 = fromList transition0705Input0 + fromList transition0705Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0705Chunk0, transition0705Chunk1]
  have hn : (transition0705Raw0 : Multiset ℕ) + (transition0705Raw1 : Multiset ℕ) = 1 • (supportNumbers0158 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0158] using hm

private def transition0706Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition0706Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 144, 145, 146, 147, 148, 149, 150, 151, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0706Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0706Input0) = fromList transition0706Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0706Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0706Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 72, 73, 74, 75, 76, 77, 78, 79, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0706Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0706Input1) = fromList transition0706Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0706 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0090 = 1 • support0157 := by
  have hs : support0090 = fromList transition0706Input0 + fromList transition0706Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0706Chunk0, transition0706Chunk1]
  have hn : (transition0706Raw0 : Multiset ℕ) + (transition0706Raw1 : Multiset ℕ) = 1 • (supportNumbers0157 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0157] using hm

private def transition0707Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0707Raw0 : List ℕ := [0, 1, 4, 5, 8, 9, 12, 13, 64, 65, 68, 69, 72, 73, 76, 77, 144, 145, 148, 149, 152, 153, 156, 157, 208, 209, 212, 213, 216, 217, 220, 221]
private theorem transition0707Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0707Input0) = fromList transition0707Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0707 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0157 = 1 • support0988 := by
  have hs : support0157 = fromList transition0707Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0707Chunk0]
  have hn : (transition0707Raw0 : Multiset ℕ) = 1 • (supportNumbers0988 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0988] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
