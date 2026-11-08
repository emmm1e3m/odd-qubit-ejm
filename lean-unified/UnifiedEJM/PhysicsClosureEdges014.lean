import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0293Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 544, 545, 546, 547, 552, 553, 554, 555, 564, 565, 566, 567, 572, 573, 574, 575, 672, 673, 674, 675, 680, 681, 682, 683, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition0293Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 20, 596, 21, 597, 22, 598, 23, 599, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 308, 884, 309, 885, 310, 886, 311, 887, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0293Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0293Input0) = fromList transition0293Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0293 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0720 = 1 • support0508 := by
  have hs : support0720 = fromList transition0293Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0293Chunk0]
  have hn : (transition0293Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0294Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0294Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition0294Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0294Input0) = fromList transition0294Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0294Input1 : List ℕ := [512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0294Raw1 : List ℕ := [256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0294Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0294Input1) = fromList transition0294Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0294 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0037 = 2 • support0036 := by
  have hs : support0037 = fromList transition0294Input0 + fromList transition0294Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0294Chunk0, transition0294Chunk1]
  have hn : (transition0294Raw0 : Multiset ℕ) + (transition0294Raw1 : Multiset ℕ) = 2 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0295Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0295Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543]
private theorem transition0295Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0295Input0) = fromList transition0295Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0295Input1 : List ℕ := [512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0295Raw1 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0295Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0295Input1) = fromList transition0295Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0295 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0037 = 2 • support0037 := by
  have hs : support0037 = fromList transition0295Input0 + fromList transition0295Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0295Chunk0, transition0295Chunk1]
  have hn : (transition0295Raw0 : Multiset ℕ) + (transition0295Raw1 : Multiset ℕ) = 2 • (supportNumbers0037 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0037] using hm

private def transition0296Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0296Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition0296Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0296Input0) = fromList transition0296Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0296Input1 : List ℕ := [512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0296Raw1 : List ℕ := [256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition0296Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0296Input1) = fromList transition0296Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0296 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0037 = 2 • support0036 := by
  have hs : support0037 = fromList transition0296Input0 + fromList transition0296Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0296Chunk0, transition0296Chunk1]
  have hn : (transition0296Raw0 : Multiset ℕ) + (transition0296Raw1 : Multiset ℕ) = 2 • (supportNumbers0036 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0036] using hm

private def transition0297Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private def transition0297Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703]
private theorem transition0297Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0297Input0) = fromList transition0297Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0297Input1 : List ℕ := [512, 513, 514, 515, 520, 521, 522, 523, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 768, 769, 770, 771, 776, 777, 778, 779, 788, 789, 790, 791, 796, 797, 798, 799, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition0297Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0297Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0297Input1) = fromList transition0297Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0297 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0037 = 2 • support0593 := by
  have hs : support0037 = fromList transition0297Input0 + fromList transition0297Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0297Chunk0, transition0297Chunk1]
  have hn : (transition0297Raw0 : Multiset ℕ) + (transition0297Raw1 : Multiset ℕ) = 2 • (supportNumbers0593 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0593] using hm

private def transition0298Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0298Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0298Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0298Input0) = fromList transition0298Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0298 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0298Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0298Chunk0]
  have hn : (transition0298Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0299Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0299Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711]
private theorem transition0299Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0299Input0) = fromList transition0299Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0299 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0016 = 1 • support0075 := by
  have hs : support0016 = fromList transition0299Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0299Chunk0]
  have hn : (transition0299Raw0 : Multiset ℕ) = 1 • (supportNumbers0075 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0075] using hm

private def transition0300Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0300Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0300Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0300Input0) = fromList transition0300Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0300 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0016 = 1 • support0016 := by
  have hs : support0016 = fromList transition0300Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0300Chunk0]
  have hn : (transition0300Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0301Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private def transition0301Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615]
private theorem transition0301Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0301Input0) = fromList transition0301Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0301 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0016 = 1 • support0721 := by
  have hs : support0016 = fromList transition0301Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0301Chunk0]
  have hn : (transition0301Raw0 : Multiset ℕ) = 1 • (supportNumbers0721 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0721] using hm

private def transition0302Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 544, 546, 548, 550, 609, 611, 613, 615]
private def transition0302Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 288, 290, 292, 294, 353, 355, 357, 359]
private theorem transition0302Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0302Input0) = fromList transition0302Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0302 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0721 = 1 • support0722 := by
  have hs : support0721 = fromList transition0302Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0302Chunk0]
  have hn : (transition0302Raw0 : Multiset ℕ) = 1 • (supportNumbers0722 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0722] using hm

private def transition0303Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 544, 546, 548, 550, 609, 611, 613, 615]
private def transition0303Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807]
private theorem transition0303Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0303Input0) = fromList transition0303Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0303 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0721 = 1 • support0724 := by
  have hs : support0721 = fromList transition0303Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0303Chunk0]
  have hn : (transition0303Raw0 : Multiset ℕ) = 1 • (supportNumbers0724 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0724] using hm

private def transition0304Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0304Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0304Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0304Input0) = fromList transition0304Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0304 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0038 = 1 • support0076 := by
  have hs : support0038 = fromList transition0304Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0304Chunk0]
  have hn : (transition0304Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0305Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0305Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0305Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0305Input0) = fromList transition0305Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0305 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0038 = 1 • support0076 := by
  have hs : support0038 = fromList transition0305Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0305Chunk0]
  have hn : (transition0305Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0306Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0306Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0306Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0306Input0) = fromList transition0306Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0306 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0038 = 1 • support0076 := by
  have hs : support0038 = fromList transition0306Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0306Chunk0]
  have hn : (transition0306Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0307Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0307Raw0 : List ℕ := [0, 4, 65, 69, 136, 140, 201, 205]
private theorem transition0307Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0307Input0) = fromList transition0307Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0307 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0076 = 1 • support0726 := by
  have hs : support0076 = fromList transition0307Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0307Chunk0]
  have hn : (transition0307Raw0 : Multiset ℕ) = 1 • (supportNumbers0726 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0726] using hm

private def transition0308Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0308Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 136, 714, 140, 718, 201, 651, 205, 655]
private theorem transition0308Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0308Input0) = fromList transition0308Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0308 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0076 = 1 • support0728 := by
  have hs : support0076 = fromList transition0308Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0308Chunk0]
  have hn : (transition0308Raw0 : Multiset ℕ) = 1 • (supportNumbers0728 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0728] using hm

private def transition0309Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463]
private def transition0309Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0309Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0309Input0) = fromList transition0309Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0309 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0038 = 1 • support0076 := by
  have hs : support0038 = fromList transition0309Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0309Chunk0]
  have hn : (transition0309Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0310Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0310Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private theorem transition0310Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0310Input0) = fromList transition0310Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0310 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0076 = 1 • support0076 := by
  have hs : support0076 = fromList transition0310Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0310Chunk0]
  have hn : (transition0310Raw0 : Multiset ℕ) = 1 • (supportNumbers0076 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0076] using hm

private def transition0311Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207]
private def transition0311Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 136, 712, 138, 714, 140, 716, 142, 718, 201, 649, 203, 651, 205, 653, 207, 655]
private theorem transition0311Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0311Input0) = fromList transition0311Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0311 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0076 = 1 • support0731 := by
  have hs : support0076 = fromList transition0311Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0311Chunk0]
  have hn : (transition0311Raw0 : Multiset ℕ) = 1 • (supportNumbers0731 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0731] using hm

private def transition0312Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 392, 394, 396, 398, 457, 459, 461, 463, 640, 642, 644, 646, 705, 707, 709, 711, 776, 778, 780, 782, 841, 843, 845, 847]
private def transition0312Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 384, 386, 388, 390, 449, 451, 453, 455, 264, 266, 268, 270, 329, 331, 333, 335]
private theorem transition0312Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0312Input0) = fromList transition0312Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0312 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0039 = 1 • support0077 := by
  have hs : support0039 = fromList transition0312Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0312Chunk0]
  have hn : (transition0312Raw0 : Multiset ℕ) = 1 • (supportNumbers0077 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0077] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
