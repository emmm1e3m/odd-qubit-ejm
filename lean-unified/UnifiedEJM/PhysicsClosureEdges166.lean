import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2833Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2833Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 152, 536, 153, 537, 154, 538, 155, 539, 156, 540, 157, 541, 158, 542, 159, 543, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591, 216, 600, 217, 601, 218, 602, 219, 603, 220, 604, 221, 605, 222, 606, 223, 607]
private theorem transition2833Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2833Input0) = fromList transition2833Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2833Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727, 776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2833Raw1 : List ℕ := [384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 400, 784, 401, 785, 402, 786, 403, 787, 404, 788, 405, 789, 406, 790, 407, 791, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 464, 848, 465, 849, 466, 850, 467, 851, 468, 852, 469, 853, 470, 854, 471, 855, 264, 904, 265, 905, 266, 906, 267, 907, 268, 908, 269, 909, 270, 910, 271, 911, 280, 920, 281, 921, 282, 922, 283, 923, 284, 924, 285, 925, 286, 926, 287, 927, 328, 968, 329, 969, 330, 970, 331, 971, 332, 972, 333, 973, 334, 974, 335, 975, 344, 984, 345, 985, 346, 986, 347, 987, 348, 988, 349, 989, 350, 990, 351, 991]
private theorem transition2833Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2833Input1) = fromList transition2833Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2833 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0417 = 1 • support0163 := by
  have hs : support0417 = fromList transition2833Input0 + fromList transition2833Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2833Chunk0, transition2833Chunk1]
  have hn : (transition2833Raw0 : Multiset ℕ) + (transition2833Raw1 : Multiset ℕ) = 1 • (supportNumbers0163 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0163] using hm

private def transition2834Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2834Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem transition2834Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2834Input0) = fromList transition2834Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2834Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727, 776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2834Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471, 264, 265, 266, 267, 268, 269, 270, 271, 280, 281, 282, 283, 284, 285, 286, 287, 328, 329, 330, 331, 332, 333, 334, 335, 344, 345, 346, 347, 348, 349, 350, 351]
private theorem transition2834Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2834Input1) = fromList transition2834Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2834 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0417 = 1 • support0162 := by
  have hs : support0417 = fromList transition2834Input0 + fromList transition2834Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2834Chunk0, transition2834Chunk1]
  have hn : (transition2834Raw0 : Multiset ℕ) + (transition2834Raw1 : Multiset ℕ) = 1 • (supportNumbers0162 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0162] using hm

private def transition2835Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 392, 393, 394, 395, 396, 397, 398, 399, 408, 409, 410, 411, 412, 413, 414, 415, 456, 457, 458, 459, 460, 461, 462, 463, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition2835Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 152, 696, 153, 697, 154, 698, 155, 699, 156, 700, 157, 701, 158, 702, 159, 703, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751, 216, 760, 217, 761, 218, 762, 219, 763, 220, 764, 221, 765, 222, 766, 223, 767]
private theorem transition2835Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2835Input0) = fromList transition2835Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2835Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727, 776, 777, 778, 779, 780, 781, 782, 783, 792, 793, 794, 795, 796, 797, 798, 799, 840, 841, 842, 843, 844, 845, 846, 847, 856, 857, 858, 859, 860, 861, 862, 863]
private def transition2835Raw1 : List ℕ := [384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015, 264, 808, 265, 809, 266, 810, 267, 811, 268, 812, 269, 813, 270, 814, 271, 815, 280, 824, 281, 825, 282, 826, 283, 827, 284, 828, 285, 829, 286, 830, 287, 831, 328, 872, 329, 873, 330, 874, 331, 875, 332, 876, 333, 877, 334, 878, 335, 879, 344, 888, 345, 889, 346, 890, 347, 891, 348, 892, 349, 893, 350, 894, 351, 895]
private theorem transition2835Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2835Input1) = fromList transition2835Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2835 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0417 = 1 • support1009 := by
  have hs : support0417 = fromList transition2835Input0 + fromList transition2835Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2835Chunk0, transition2835Chunk1]
  have hn : (transition2835Raw0 : Multiset ℕ) + (transition2835Raw1 : Multiset ℕ) = 1 • (supportNumbers1009 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1009] using hm

private def transition2836Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2836Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition2836Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2836Input0) = fromList transition2836Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2836 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0418 = 1 • support0053 := by
  have hs : support0418 = fromList transition2836Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2836Chunk0]
  have hn : (transition2836Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition2837Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2837Raw0 : List ℕ := [0, 2, 520, 522, 640, 642, 136, 138]
private theorem transition2837Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2837Input0) = fromList transition2837Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2837 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0418 = 1 • support0101 := by
  have hs : support0418 = fromList transition2837Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2837Chunk0]
  have hn : (transition2837Raw0 : Multiset ℕ) = 1 • (supportNumbers0101 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0101] using hm

private def transition2838Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2838Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition2838Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2838Input0) = fromList transition2838Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2838 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0418 = 1 • support0053 := by
  have hs : support0418 = fromList transition2838Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2838Chunk0]
  have hn : (transition2838Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition2839Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394]
private def transition2839Raw0 : List ℕ := [0, 2, 680, 682, 544, 546, 136, 138]
private theorem transition2839Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2839Input0) = fromList transition2839Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2839 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0418 = 1 • support0806 := by
  have hs : support0418 = fromList transition2839Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2839Chunk0]
  have hn : (transition2839Raw0 : Multiset ℕ) = 1 • (supportNumbers0806 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0806] using hm

private def transition2840Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 520, 522, 640, 642, 776, 778, 896, 898]
private def transition2840Raw0 : List ℕ := [0, 2, 136, 138, 0, 2, 136, 138, 264, 266, 384, 386, 264, 266, 384, 386]
private theorem transition2840Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2840Input0) = fromList transition2840Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2840 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0419 = 2 • support0054 := by
  have hs : support0419 = fromList transition2840Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2840Chunk0]
  have hn : (transition2840Raw0 : Multiset ℕ) = 2 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition2841Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 520, 522, 640, 642, 776, 778, 896, 898]
private def transition2841Raw0 : List ℕ := [0, 640, 2, 642, 136, 520, 138, 522, 0, 640, 2, 642, 136, 520, 138, 522, 264, 904, 266, 906, 384, 768, 386, 770, 264, 904, 266, 906, 384, 768, 386, 770]
private theorem transition2841Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2841Input0) = fromList transition2841Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2841 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0419 = 2 • support0055 := by
  have hs : support0419 = fromList transition2841Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2841Chunk0]
  have hn : (transition2841Raw0 : Multiset ℕ) = 2 • (supportNumbers0055 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0055] using hm

private def transition2842Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 520, 522, 640, 642, 776, 778, 896, 898]
private def transition2842Raw0 : List ℕ := [0, 2, 136, 138, 0, 2, 136, 138, 264, 266, 384, 386, 264, 266, 384, 386]
private theorem transition2842Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2842Input0) = fromList transition2842Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2842 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0419 = 2 • support0054 := by
  have hs : support0419 = fromList transition2842Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2842Chunk0]
  have hn : (transition2842Raw0 : Multiset ℕ) = 2 • (supportNumbers0054 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0054] using hm

private def transition2843Input0 : List ℕ := [0, 2, 136, 138, 256, 258, 392, 394, 520, 522, 640, 642, 776, 778, 896, 898]
private def transition2843Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 0, 544, 2, 546, 136, 680, 138, 682, 264, 808, 266, 810, 384, 928, 386, 930, 264, 808, 266, 810, 384, 928, 386, 930]
private theorem transition2843Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2843Input0) = fromList transition2843Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2843 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0419 = 2 • support0656 := by
  have hs : support0419 = fromList transition2843Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2843Chunk0]
  have hn : (transition2843Raw0 : Multiset ℕ) = 2 • (supportNumbers0656 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0656] using hm

private def transition2844Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2844Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition2844Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2844Input0) = fromList transition2844Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2844 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0420 = 1 • support0175 := by
  have hs : support0420 = fromList transition2844Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2844Chunk0]
  have hn : (transition2844Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition2845Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2845Raw0 : List ℕ := [0, 2, 521, 523, 9, 11, 512, 514]
private theorem transition2845Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2845Input0) = fromList transition2845Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2845 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0420 = 1 • support1737 := by
  have hs : support0420 = fromList transition2845Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2845Chunk0]
  have hn : (transition2845Raw0 : Multiset ℕ) = 1 • (supportNumbers1737 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1737] using hm

private def transition2846Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2846Raw0 : List ℕ := [0, 2, 9, 11]
private theorem transition2846Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2846Input0) = fromList transition2846Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2846 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0420 = 1 • support0175 := by
  have hs : support0420 = fromList transition2846Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2846Chunk0]
  have hn : (transition2846Raw0 : Multiset ℕ) = 1 • (supportNumbers0175 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0175] using hm

private def transition2847Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2847Raw0 : List ℕ := [0, 2, 681, 683, 9, 11, 672, 674]
private theorem transition2847Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2847Input0) = fromList transition2847Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2847 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0420 = 1 • support1738 := by
  have hs : support0420 = fromList transition2847Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2847Chunk0]
  have hn : (transition2847Raw0 : Multiset ℕ) = 1 • (supportNumbers1738 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1738] using hm

private def transition2848Input0 : List ℕ := [0, 2, 9, 11, 672, 674, 681, 683]
private def transition2848Raw0 : List ℕ := [0, 2, 9, 11, 416, 418, 425, 427]
private theorem transition2848Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2848Input0) = fromList transition2848Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2848 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1738 = 1 • support1739 := by
  have hs : support1738 = fromList transition2848Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2848Chunk0]
  have hn : (transition2848Raw0 : Multiset ℕ) = 1 • (supportNumbers1739 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1739] using hm

private def transition2849Input0 : List ℕ := [0, 2, 9, 11, 672, 674, 681, 683]
private def transition2849Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition2849Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2849Input0) = fromList transition2849Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2849 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1738 = 1 • support1740 := by
  have hs : support1738 = fromList transition2849Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2849Chunk0]
  have hn : (transition2849Raw0 : Multiset ℕ) = 1 • (supportNumbers1740 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1740] using hm

private def transition2850Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 521, 523, 640, 642, 768, 770, 905, 907]
private def transition2850Raw0 : List ℕ := [0, 2, 137, 139, 9, 11, 128, 130, 265, 267, 384, 386, 256, 258, 393, 395]
private theorem transition2850Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2850Input0) = fromList transition2850Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2850 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0421 = 1 • support0261 := by
  have hs : support0421 = fromList transition2850Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2850Chunk0]
  have hn : (transition2850Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition2851Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 521, 523, 640, 642, 768, 770, 905, 907]
private def transition2851Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 9, 649, 11, 651, 128, 512, 130, 514, 265, 905, 267, 907, 384, 768, 386, 770, 256, 896, 258, 898, 393, 777, 395, 779]
private theorem transition2851Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2851Input0) = fromList transition2851Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2851 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0421 = 1 • support0262 := by
  have hs : support0421 = fromList transition2851Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2851Chunk0]
  have hn : (transition2851Raw0 : Multiset ℕ) = 1 • (supportNumbers0262 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0262] using hm

private def transition2852Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 521, 523, 640, 642, 768, 770, 905, 907]
private def transition2852Raw0 : List ℕ := [0, 2, 137, 139, 9, 11, 128, 130, 265, 267, 384, 386, 256, 258, 393, 395]
private theorem transition2852Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2852Input0) = fromList transition2852Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2852 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0421 = 1 • support0261 := by
  have hs : support0421 = fromList transition2852Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2852Chunk0]
  have hn : (transition2852Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition2853Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 521, 523, 640, 642, 768, 770, 905, 907]
private def transition2853Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 9, 553, 11, 555, 128, 672, 130, 674, 265, 809, 267, 811, 384, 928, 386, 930, 256, 800, 258, 802, 393, 937, 395, 939]
private theorem transition2853Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2853Input0) = fromList transition2853Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2853 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0421 = 1 • support1289 := by
  have hs : support0421 = fromList transition2853Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2853Chunk0]
  have hn : (transition2853Raw0 : Multiset ℕ) = 1 • (supportNumbers1289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1289] using hm

private def transition2854Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2854Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition2854Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2854Input0) = fromList transition2854Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2854 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0422 = 1 • support0059 := by
  have hs : support0422 = fromList transition2854Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2854Chunk0]
  have hn : (transition2854Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition2855Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2855Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition2855Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2855Input0) = fromList transition2855Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2855 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0422 = 1 • support0059 := by
  have hs : support0422 = fromList transition2855Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2855Chunk0]
  have hn : (transition2855Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition2856Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2856Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition2856Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2856Input0) = fromList transition2856Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2856 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0422 = 1 • support0059 := by
  have hs : support0422 = fromList transition2856Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2856Chunk0]
  have hn : (transition2856Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition2857Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2857Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138]
private theorem transition2857Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2857Input0) = fromList transition2857Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2857 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0422 = 1 • support0059 := by
  have hs : support0422 = fromList transition2857Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2857Chunk0]
  have hn : (transition2857Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition2858Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition2858Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private theorem transition2858Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2858Input0) = fromList transition2858Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2858 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0059 = 1 • support0059 := by
  have hs : support0059 = fromList transition2858Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2858Chunk0]
  have hn : (transition2858Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition2859Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition2859Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714]
private theorem transition2859Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2859Input0) = fromList transition2859Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2859 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0059 = 1 • support0838 := by
  have hs : support0059 = fromList transition2859Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2859Chunk0]
  have hn : (transition2859Raw0 : Multiset ℕ) = 1 • (supportNumbers0838 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0838] using hm

private def transition2860Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 513, 515, 640, 642, 776, 778, 905, 907]
private def transition2860Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138, 257, 259, 384, 386, 264, 266, 393, 395]
private theorem transition2860Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2860Input0) = fromList transition2860Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2860 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0423 = 1 • support0185 := by
  have hs : support0423 = fromList transition2860Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2860Chunk0]
  have hn : (transition2860Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition2861Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 513, 515, 640, 642, 776, 778, 905, 907]
private def transition2861Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 9, 649, 11, 651, 136, 520, 138, 522, 257, 897, 259, 899, 384, 768, 386, 770, 264, 904, 266, 906, 393, 777, 395, 779]
private theorem transition2861Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2861Input0) = fromList transition2861Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2861 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0423 = 1 • support0186 := by
  have hs : support0423 = fromList transition2861Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2861Chunk0]
  have hn : (transition2861Raw0 : Multiset ℕ) = 1 • (supportNumbers0186 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0186] using hm

private def transition2862Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 513, 515, 640, 642, 776, 778, 905, 907]
private def transition2862Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138, 257, 259, 384, 386, 264, 266, 393, 395]
private theorem transition2862Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2862Input0) = fromList transition2862Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2862 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0423 = 1 • support0185 := by
  have hs : support0423 = fromList transition2862Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2862Chunk0]
  have hn : (transition2862Raw0 : Multiset ℕ) = 1 • (supportNumbers0185 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0185] using hm

private def transition2863Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 513, 515, 640, 642, 776, 778, 905, 907]
private def transition2863Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 9, 553, 11, 555, 136, 680, 138, 682, 257, 801, 259, 803, 384, 928, 386, 930, 264, 808, 266, 810, 393, 937, 395, 939]
private theorem transition2863Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2863Input0) = fromList transition2863Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2863 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0423 = 1 • support1071 := by
  have hs : support0423 = fromList transition2863Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2863Chunk0]
  have hn : (transition2863Raw0 : Multiset ℕ) = 1 • (supportNumbers1071 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1071] using hm

private def transition2864Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 512, 513, 514, 515, 668, 669, 670, 671]
private def transition2864Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private theorem transition2864Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2864Input0) = fromList transition2864Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2864 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0424 = 1 • support0459 := by
  have hs : support0424 = fromList transition2864Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2864Chunk0]
  have hn : (transition2864Raw0 : Multiset ℕ) = 1 • (supportNumbers0459 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0459] using hm

private def transition2865Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 512, 513, 514, 515, 668, 669, 670, 671]
private def transition2865Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2865Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2865Input0) = fromList transition2865Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2865 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0424 = 1 • support0460 := by
  have hs : support0424 = fromList transition2865Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2865Chunk0]
  have hn : (transition2865Raw0 : Multiset ℕ) = 1 • (supportNumbers0460 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0460] using hm

private def transition2866Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 512, 513, 514, 515, 668, 669, 670, 671]
private def transition2866Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private theorem transition2866Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2866Input0) = fromList transition2866Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2866 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0424 = 1 • support0459 := by
  have hs : support0424 = fromList transition2866Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2866Chunk0]
  have hn : (transition2866Raw0 : Multiset ℕ) = 1 • (supportNumbers0459 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0459] using hm

private def transition2867Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition2867Raw0 : List ℕ := [0, 1, 156, 157, 2, 3, 158, 159]
private theorem transition2867Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2867Input0) = fromList transition2867Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2867 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0459 = 1 • support0117 := by
  have hs : support0459 = fromList transition2867Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2867Chunk0]
  have hn : (transition2867Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition2868Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 256, 257, 258, 259, 412, 413, 414, 415]
private def transition2868Raw0 : List ℕ := [0, 1, 578, 579, 156, 157, 734, 735, 576, 577, 2, 3, 732, 733, 158, 159]
private theorem transition2868Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2868Input0) = fromList transition2868Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2868 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0459 = 1 • support0854 := by
  have hs : support0459 = fromList transition2868Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2868Chunk0]
  have hn : (transition2868Raw0 : Multiset ℕ) = 1 • (supportNumbers0854 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0854] using hm

private def transition2869Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 512, 513, 514, 515, 668, 669, 670, 671]
private def transition2869Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2869Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2869Input0) = fromList transition2869Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2869 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0424 = 1 • support1742 := by
  have hs : support0424 = fromList transition2869Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2869Chunk0]
  have hn : (transition2869Raw0 : Multiset ℕ) = 1 • (supportNumbers1742 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1742] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
