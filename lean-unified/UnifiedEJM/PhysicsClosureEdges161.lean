import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2803Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2803Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 144, 528, 145, 529, 146, 530, 147, 531, 148, 532, 149, 533, 150, 534, 151, 535, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 208, 592, 209, 593, 210, 594, 211, 595, 212, 596, 213, 597, 214, 598, 215, 599]
private theorem transition2803Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2803Input0) = fromList transition2803Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2803Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition2803Raw1 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991, 392, 776, 393, 777, 394, 778, 395, 779, 396, 780, 397, 781, 398, 782, 399, 783, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 456, 840, 457, 841, 458, 842, 459, 843, 460, 844, 461, 845, 462, 846, 463, 847, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855]
private theorem transition2803Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2803Input1) = fromList transition2803Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2803 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0412 = 1 • support0456 := by
  have hs : support0412 = fromList transition2803Input0 + fromList transition2803Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2803Chunk0, transition2803Chunk1]
  have hn : (transition2803Raw0 : Multiset ℕ) + (transition2803Raw1 : Multiset ℕ) = 1 • (supportNumbers0456 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0456] using hm

private def transition2804Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2804Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2804Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2804Input0) = fromList transition2804Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2804Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition2804Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private theorem transition2804Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2804Input1) = fromList transition2804Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2804 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0412 = 1 • support0455 := by
  have hs : support0412 = fromList transition2804Input0 + fromList transition2804Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2804Chunk0, transition2804Chunk1]
  have hn : (transition2804Raw0 : Multiset ℕ) + (transition2804Raw1 : Multiset ℕ) = 1 • (supportNumbers0455 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0455] using hm

private def transition2805Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2805Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213]
private theorem transition2805Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2805Input0) = fromList transition2805Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2805Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2805Raw1 : List ℕ := [2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215]
private theorem transition2805Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2805Input1) = fromList transition2805Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2805 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0455 = 1 • support0411 := by
  have hs : support0455 = fromList transition2805Input0 + fromList transition2805Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2805Chunk0, transition2805Chunk1]
  have hn : (transition2805Raw0 : Multiset ℕ) + (transition2805Raw1 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def transition2806Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2806Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 24, 25, 602, 603, 28, 29, 606, 607, 64, 65, 514, 515, 68, 69, 518, 519, 88, 89, 538, 539, 92, 93, 542, 543, 136, 137, 714, 715, 140, 141, 718, 719, 144, 145, 722, 723, 148, 149, 726, 727, 200, 201, 650, 651, 204, 205, 654, 655, 208, 209, 658, 659, 212, 213, 662, 663]
private theorem transition2806Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2806Input0) = fromList transition2806Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2806Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2806Raw1 : List ℕ := [576, 577, 2, 3, 580, 581, 6, 7, 600, 601, 26, 27, 604, 605, 30, 31, 512, 513, 66, 67, 516, 517, 70, 71, 536, 537, 90, 91, 540, 541, 94, 95, 712, 713, 138, 139, 716, 717, 142, 143, 720, 721, 146, 147, 724, 725, 150, 151, 648, 649, 202, 203, 652, 653, 206, 207, 656, 657, 210, 211, 660, 661, 214, 215]
private theorem transition2806Chunk1 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2806Input1) = fromList transition2806Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2806 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0455 = 1 • support0412 := by
  have hs : support0455 = fromList transition2806Input0 + fromList transition2806Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2806Chunk0, transition2806Chunk1]
  have hn : (transition2806Raw0 : Multiset ℕ) + (transition2806Raw1 : Multiset ℕ) = 1 • (supportNumbers0412 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0412] using hm

private def transition2807Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2807Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 24, 568, 25, 569, 26, 570, 27, 571, 28, 572, 29, 573, 30, 574, 31, 575, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 88, 632, 89, 633, 90, 634, 91, 635, 92, 636, 93, 637, 94, 638, 95, 639, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 144, 688, 145, 689, 146, 690, 147, 691, 148, 692, 149, 693, 150, 694, 151, 695, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 208, 752, 209, 753, 210, 754, 211, 755, 212, 756, 213, 757, 214, 758, 215, 759]
private theorem transition2807Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2807Input0) = fromList transition2807Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2807Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition2807Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895, 392, 936, 393, 937, 394, 938, 395, 939, 396, 940, 397, 941, 398, 942, 399, 943, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 456, 1000, 457, 1001, 458, 1002, 459, 1003, 460, 1004, 461, 1005, 462, 1006, 463, 1007, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition2807Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2807Input1) = fromList transition2807Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2807 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0412 = 1 • support1735 := by
  have hs : support0412 = fromList transition2807Input0 + fromList transition2807Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2807Chunk0, transition2807Chunk1]
  have hn : (transition2807Raw0 : Multiset ℕ) + (transition2807Raw1 : Multiset ℕ) = 1 • (supportNumbers1735 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1735] using hm

private def transition2808Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def transition2808Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2808Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2808Input0) = fromList transition2808Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2808Input1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 280, 281, 282, 283, 284, 285, 286, 287, 320, 321, 322, 323, 324, 325, 326, 327, 344, 345, 346, 347, 348, 349, 350, 351, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition2808Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition2808Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2808Input1) = fromList transition2808Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2808Input2 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 568, 569, 570, 571, 572, 573, 574, 575, 608, 609, 610, 611, 612, 613, 614, 615, 632, 633, 634, 635, 636, 637, 638, 639, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition2808Raw2 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition2808Chunk2 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2808Input2) = fromList transition2808Raw2 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2808Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 888, 889, 890, 891, 892, 893, 894, 895, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition2808Raw3 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition2808Chunk3 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2808Input3) = fromList transition2808Raw3 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2808 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1735 = 2 • support0630 := by
  have hs : support1735 = fromList transition2808Input0 + fromList transition2808Input1 + fromList transition2808Input2 + fromList transition2808Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2808Chunk0, transition2808Chunk1, transition2808Chunk2, transition2808Chunk3]
  have hn : (transition2808Raw0 : Multiset ℕ) + (transition2808Raw1 : Multiset ℕ) + (transition2808Raw2 : Multiset ℕ) + (transition2808Raw3 : Multiset ℕ) = 2 • (supportNumbers0630 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0630] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
