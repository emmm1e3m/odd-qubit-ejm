import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0389Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0389Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition0389Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0389Input0) = fromList transition0389Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0389Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0389Raw1 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 272, 912, 273, 913, 274, 914, 275, 915, 276, 916, 277, 917, 278, 918, 279, 919, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 336, 976, 337, 977, 338, 978, 339, 979, 340, 980, 341, 981, 342, 982, 343, 983, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition0389Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0389Input1) = fromList transition0389Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0389 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0049 = 1 • support0095 := by
  have hs : support0049 = fromList transition0389Input0 + fromList transition0389Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0389Chunk0, transition0389Chunk1]
  have hn : (transition0389Raw0 : Multiset ℕ) + (transition0389Raw1 : Multiset ℕ) = 1 • (supportNumbers0095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0095] using hm

private def transition0390Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0390Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0390Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0390Input0) = fromList transition0390Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0390Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0390Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0390Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0390Input1) = fromList transition0390Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0390 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0049 = 1 • support0094 := by
  have hs : support0049 = fromList transition0390Input0 + fromList transition0390Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0390Chunk0, transition0390Chunk1]
  have hn : (transition0390Raw0 : Multiset ℕ) + (transition0390Raw1 : Multiset ℕ) = 1 • (supportNumbers0094 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0094] using hm

private def transition0391Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0391Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221]
private theorem transition0391Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0391Input0) = fromList transition0391Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0391Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0391Raw1 : List ℕ := [2, 3, 6, 7, 18, 19, 22, 23, 66, 67, 70, 71, 82, 83, 86, 87, 138, 139, 142, 143, 154, 155, 158, 159, 202, 203, 206, 207, 218, 219, 222, 223]
private theorem transition0391Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0391Input1) = fromList transition0391Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0391 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0094 = 1 • support0048 := by
  have hs : support0094 = fromList transition0391Input0 + fromList transition0391Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0391Chunk0, transition0391Chunk1]
  have hn : (transition0391Raw0 : Multiset ℕ) + (transition0391Raw1 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def transition0392Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0392Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 16, 17, 594, 595, 20, 21, 598, 599, 64, 65, 514, 515, 68, 69, 518, 519, 80, 81, 530, 531, 84, 85, 534, 535, 136, 137, 714, 715, 140, 141, 718, 719, 152, 153, 730, 731, 156, 157, 734, 735, 200, 201, 650, 651, 204, 205, 654, 655, 216, 217, 666, 667, 220, 221, 670, 671]
private theorem transition0392Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0392Input0) = fromList transition0392Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0392Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0392Raw1 : List ℕ := [576, 577, 2, 3, 580, 581, 6, 7, 592, 593, 18, 19, 596, 597, 22, 23, 512, 513, 66, 67, 516, 517, 70, 71, 528, 529, 82, 83, 532, 533, 86, 87, 712, 713, 138, 139, 716, 717, 142, 143, 728, 729, 154, 155, 732, 733, 158, 159, 648, 649, 202, 203, 652, 653, 206, 207, 664, 665, 218, 219, 668, 669, 222, 223]
private theorem transition0392Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0392Input1) = fromList transition0392Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0392 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0094 = 1 • support0049 := by
  have hs : support0094 = fromList transition0392Input0 + fromList transition0392Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0392Chunk0, transition0392Chunk1]
  have hn : (transition0392Raw0 : Multiset ℕ) + (transition0392Raw1 : Multiset ℕ) = 1 • (supportNumbers0049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0049] using hm

private def transition0393Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0393Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition0393Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0393Input0) = fromList transition0393Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0393Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0393Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 272, 816, 273, 817, 274, 818, 275, 819, 276, 820, 277, 821, 278, 822, 279, 823, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 336, 880, 337, 881, 338, 882, 339, 883, 340, 884, 341, 885, 342, 886, 343, 887, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0393Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0393Input1) = fromList transition0393Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0393 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0049 = 1 • support0786 := by
  have hs : support0049 = fromList transition0393Input0 + fromList transition0393Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0393Chunk0, transition0393Chunk1]
  have hn : (transition0393Raw0 : Multiset ℕ) + (transition0393Raw1 : Multiset ℕ) = 1 • (supportNumbers0786 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0786] using hm

private def transition0394Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def transition0394Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0394Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0394Input0) = fromList transition0394Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0394Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 272, 273, 274, 275, 276, 277, 278, 279, 320, 321, 322, 323, 324, 325, 326, 327, 336, 337, 338, 339, 340, 341, 342, 343, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0394Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition0394Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0394Input1) = fromList transition0394Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0394Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 680, 681, 682, 683, 684, 685, 686, 687, 696, 697, 698, 699, 700, 701, 702, 703, 744, 745, 746, 747, 748, 749, 750, 751, 760, 761, 762, 763, 764, 765, 766, 767]
private def transition0394Raw2 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition0394Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0394Input2) = fromList transition0394Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0394Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 816, 817, 818, 819, 820, 821, 822, 823, 864, 865, 866, 867, 868, 869, 870, 871, 880, 881, 882, 883, 884, 885, 886, 887, 936, 937, 938, 939, 940, 941, 942, 943, 952, 953, 954, 955, 956, 957, 958, 959, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0394Raw3 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 424, 425, 426, 427, 428, 429, 430, 431, 440, 441, 442, 443, 444, 445, 446, 447, 488, 489, 490, 491, 492, 493, 494, 495, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition0394Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0394Input3) = fromList transition0394Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0394 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0786 = 2 • support0787 := by
  have hs : support0786 = fromList transition0394Input0 + fromList transition0394Input1 + fromList transition0394Input2 + fromList transition0394Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0394Chunk0, transition0394Chunk1, transition0394Chunk2, transition0394Chunk3]
  have hn : (transition0394Raw0 : Multiset ℕ) + (transition0394Raw1 : Multiset ℕ) + (transition0394Raw2 : Multiset ℕ) + (transition0394Raw3 : Multiset ℕ) = 2 • (supportNumbers0787 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0787] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
