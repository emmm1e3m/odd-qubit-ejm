import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1200Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1200Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1200Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1200Input0) = fromList transition1200Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1200Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1200Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition1200Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1200Input1) = fromList transition1200Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1200 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0161 = 1 • support0162 := by
  have hs : support0161 = fromList transition1200Input0 + fromList transition1200Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1200Chunk0, transition1200Chunk1]
  have hn : (transition1200Raw0 : Multiset ℕ) + (transition1200Raw1 : Multiset ℕ) = 1 • (supportNumbers0162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0162] using hm

private def transition1201Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1201Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition1201Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1201Input0) = fromList transition1201Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1201Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1201Raw1 : List ℕ := [264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition1201Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1201Input1) = fromList transition1201Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1201 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0161 = 1 • support0163 := by
  have hs : support0161 = fromList transition1201Input0 + fromList transition1201Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1201Chunk0, transition1201Chunk1]
  have hn : (transition1201Raw0 : Multiset ℕ) + (transition1201Raw1 : Multiset ℕ) = 1 • (supportNumbers0163 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0163] using hm

private def transition1202Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1202Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition1202Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1202Input0) = fromList transition1202Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1202Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1202Raw1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition1202Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1202Input1) = fromList transition1202Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1202 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0161 = 1 • support0162 := by
  have hs : support0161 = fromList transition1202Input0 + fromList transition1202Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1202Chunk0, transition1202Chunk1]
  have hn : (transition1202Raw0 : Multiset ℕ) + (transition1202Raw1 : Multiset ℕ) = 1 • (supportNumbers0162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0162] using hm

private def transition1203Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1203Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition1203Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1203Input0) = fromList transition1203Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1203Input1 : List ℕ := [520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1203Raw1 : List ℕ := [264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition1203Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1203Input1) = fromList transition1203Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1203 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0161 = 1 • support1009 := by
  have hs : support0161 = fromList transition1203Input0 + fromList transition1203Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1203Chunk0, transition1203Chunk1]
  have hn : (transition1203Raw0 : Multiset ℕ) + (transition1203Raw1 : Multiset ℕ) = 1 • (supportNumbers1009 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1009] using hm

private def transition1204Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1204Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition1204Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1204Input0) = fromList transition1204Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1204Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition1204Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1204Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1204Input1) = fromList transition1204Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1204 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0162 = 1 • support0246 := by
  have hs : support0162 = fromList transition1204Input0 + fromList transition1204Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1204Chunk0, transition1204Chunk1]
  have hn : (transition1204Raw0 : Multiset ℕ) + (transition1204Raw1 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm

private def transition1205Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1205Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 520, 521, 522, 523, 524, 525, 526, 527, 536, 537, 538, 539, 540, 541, 542, 543, 584, 585, 586, 587, 588, 589, 590, 591, 600, 601, 602, 603, 604, 605, 606, 607]
private theorem transition1205Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1205Input0) = fromList transition1205Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1205Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition1205Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95, 512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599]
private theorem transition1205Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1205Input1) = fromList transition1205Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1205 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0162 = 1 • support0247 := by
  have hs : support0162 = fromList transition1205Input0 + fromList transition1205Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1205Chunk0, transition1205Chunk1]
  have hn : (transition1205Raw0 : Multiset ℕ) + (transition1205Raw1 : Multiset ℕ) = 1 • (supportNumbers0247 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0247] using hm

private def transition1206Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition1206Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition1206Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1206Input0) = fromList transition1206Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1206Input1 : List ℕ := [264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition1206Raw1 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31, 72, 73, 74, 75, 76, 77, 78, 79, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1206Chunk1 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1206Input1) = fromList transition1206Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1206 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0162 = 1 • support0246 := by
  have hs : support0162 = fromList transition1206Input0 + fromList transition1206Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1206Chunk0, transition1206Chunk1]
  have hn : (transition1206Raw0 : Multiset ℕ) + (transition1206Raw1 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
