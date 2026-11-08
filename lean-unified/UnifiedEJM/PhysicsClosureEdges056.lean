import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0985Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 520, 521, 522, 523, 540, 541, 542, 543, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0985Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 264, 904, 265, 905, 266, 906, 267, 907, 284, 924, 285, 925, 286, 926, 287, 927, 392, 776, 393, 777, 394, 778, 395, 779, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition0985Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0985Input0) = fromList transition0985Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0985 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0131 = 1 • support0207 := by
  have hs : support0131 = fromList transition0985Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0985Chunk0]
  have hn : (transition0985Raw0 : Multiset ℕ) = 1 • (supportNumbers0207 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0207] using hm

private def transition0986Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 520, 521, 522, 523, 540, 541, 542, 543, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0986Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private theorem transition0986Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0986Input0) = fromList transition0986Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0986 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0131 = 1 • support0206 := by
  have hs : support0131 = fromList transition0986Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0986Chunk0]
  have hn : (transition0986Raw0 : Multiset ℕ) = 1 • (supportNumbers0206 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0206] using hm

private def transition0987Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0987Raw0 : List ℕ := [0, 1, 20, 21, 128, 129, 148, 149, 10, 11, 30, 31, 138, 139, 158, 159]
private theorem transition0987Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0987Input0) = fromList transition0987Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0987 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0206 = 1 • support1135 := by
  have hs : support0206 = fromList transition0987Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0987Chunk0]
  have hn : (transition0987Raw0 : Multiset ℕ) = 1 • (supportNumbers1135 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1135] using hm

private def transition0988Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415]
private def transition0988Raw0 : List ℕ := [0, 1, 578, 579, 20, 21, 598, 599, 128, 129, 706, 707, 148, 149, 726, 727, 584, 585, 10, 11, 604, 605, 30, 31, 712, 713, 138, 139, 732, 733, 158, 159]
private theorem transition0988Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0988Input0) = fromList transition0988Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0988 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0206 = 1 • support1137 := by
  have hs : support0206 = fromList transition0988Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0988Chunk0]
  have hn : (transition0988Raw0 : Multiset ℕ) = 1 • (supportNumbers1137 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1137] using hm

private def transition0989Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 520, 521, 522, 523, 540, 541, 542, 543, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition0989Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 264, 808, 265, 809, 266, 810, 267, 811, 284, 828, 285, 829, 286, 830, 287, 831, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition0989Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0989Input0) = fromList transition0989Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0989 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0131 = 1 • support1139 := by
  have hs : support0131 = fromList transition0989Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0989Chunk0]
  have hn : (transition0989Raw0 : Multiset ℕ) = 1 • (supportNumbers1139 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1139] using hm

private def transition0990Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695, 808, 809, 810, 811, 828, 829, 830, 831, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition0990Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 8, 9, 10, 11, 28, 29, 30, 31, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 416, 417, 418, 419, 436, 437, 438, 439, 296, 297, 298, 299, 316, 317, 318, 319, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition0990Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0990Input0) = fromList transition0990Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0990 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1139 = 1 • support0506 := by
  have hs : support1139 = fromList transition0990Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0990Chunk0]
  have hn : (transition0990Raw0 : Multiset ℕ) = 1 • (supportNumbers0506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0506] using hm

private def transition0991Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 264, 265, 266, 267, 284, 285, 286, 287, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 672, 673, 674, 675, 692, 693, 694, 695, 808, 809, 810, 811, 828, 829, 830, 831, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition0991Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 128, 704, 129, 705, 130, 706, 131, 707, 148, 724, 149, 725, 150, 726, 151, 727, 8, 584, 9, 585, 10, 586, 11, 587, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 416, 992, 417, 993, 418, 994, 419, 995, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 296, 872, 297, 873, 298, 874, 299, 875, 316, 892, 317, 893, 318, 894, 319, 895, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition0991Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0991Input0) = fromList transition0991Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0991 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1139 = 1 • support0508 := by
  have hs : support1139 = fromList transition0991Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0991Chunk0]
  have hn : (transition0991Raw0 : Multiset ℕ) = 1 • (supportNumbers0508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0508] using hm

private def transition0992Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0992Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0992Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0992Input0) = fromList transition0992Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0992 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0132 = 1 • support0016 := by
  have hs : support0132 = fromList transition0992Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0992Chunk0]
  have hn : (transition0992Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0993Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0993Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 512, 514, 516, 518, 577, 579, 581, 583]
private theorem transition0993Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0993Input0) = fromList transition0993Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0993 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0132 = 1 • support0208 := by
  have hs : support0132 = fromList transition0993Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0993Chunk0]
  have hn : (transition0993Raw0 : Multiset ℕ) = 1 • (supportNumbers0208 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0208] using hm

private def transition0994Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0994Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71]
private theorem transition0994Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0994Input0) = fromList transition0994Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0994 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0132 = 1 • support0016 := by
  have hs : support0132 = fromList transition0994Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0994Chunk0]
  have hn : (transition0994Raw0 : Multiset ℕ) = 1 • (supportNumbers0016 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0016] using hm

private def transition0995Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition0995Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 672, 674, 676, 678, 737, 739, 741, 743]
private theorem transition0995Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0995Input0) = fromList transition0995Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0995 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0132 = 1 • support1140 := by
  have hs : support0132 = fromList transition0995Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0995Chunk0]
  have hn : (transition0995Raw0 : Multiset ℕ) = 1 • (supportNumbers1140 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1140] using hm

private def transition0996Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition0996Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition0996Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0996Input0) = fromList transition0996Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0996 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1140 = 1 • support1141 := by
  have hs : support1140 = fromList transition0996Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0996Chunk0]
  have hn : (transition0996Raw0 : Multiset ℕ) = 1 • (supportNumbers1141 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1141] using hm

private def transition0997Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 672, 674, 676, 678, 737, 739, 741, 743]
private def transition0997Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition0997Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0997Input0) = fromList transition0997Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0997 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1140 = 1 • support1143 := by
  have hs : support1140 = fromList transition0997Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0997Chunk0]
  have hn : (transition0997Raw0 : Multiset ℕ) = 1 • (supportNumbers1143 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1143] using hm

private def transition0998Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839]
private def transition0998Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327]
private theorem transition0998Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0998Input0) = fromList transition0998Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0998 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0133 = 1 • support0209 := by
  have hs : support0133 = fromList transition0998Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0998Chunk0]
  have hn : (transition0998Raw0 : Multiset ℕ) = 1 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition0999Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839]
private def transition0999Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839, 256, 896, 258, 898, 260, 900, 262, 902, 321, 961, 323, 963, 325, 965, 327, 967]
private theorem transition0999Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0999Input0) = fromList transition0999Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0999 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0133 = 1 • support0210 := by
  have hs : support0133 = fromList transition0999Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0999Chunk0]
  have hn : (transition0999Raw0 : Multiset ℕ) = 1 • (supportNumbers0210 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0210] using hm

private def transition1000Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839]
private def transition1000Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327]
private theorem transition1000Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1000Input0) = fromList transition1000Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1000 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0133 = 1 • support0209 := by
  have hs : support0133 = fromList transition1000Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1000Chunk0]
  have hn : (transition1000Raw0 : Multiset ℕ) = 1 • (supportNumbers0209 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0209] using hm

private def transition1001Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1001Raw0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197, 2, 6, 67, 71, 130, 134, 195, 199]
private theorem transition1001Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1001Input0) = fromList transition1001Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1001 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0209 = 1 • support0299 := by
  have hs : support0209 = fromList transition1001Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1001Chunk0]
  have hn : (transition1001Raw0 : Multiset ℕ) = 1 • (supportNumbers0299 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0299] using hm

private def transition1002Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455]
private def transition1002Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 128, 706, 132, 710, 193, 643, 197, 647, 576, 2, 580, 6, 513, 67, 517, 71, 704, 130, 708, 134, 641, 195, 645, 199]
private theorem transition1002Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1002Input0) = fromList transition1002Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1002 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0209 = 1 • support1146 := by
  have hs : support0209 = fromList transition1002Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1002Chunk0]
  have hn : (transition1002Raw0 : Multiset ℕ) = 1 • (supportNumbers1146 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1146] using hm

private def transition1003Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 384, 386, 388, 390, 449, 451, 453, 455, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839]
private def transition1003Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871]
private theorem transition1003Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1003Input0) = fromList transition1003Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1003 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0133 = 1 • support1147 := by
  have hs : support0133 = fromList transition1003Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1003Chunk0]
  have hn : (transition1003Raw0 : Multiset ℕ) = 1 • (supportNumbers1147 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1147] using hm

private def transition1004Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 800, 802, 804, 806, 865, 867, 869, 871, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition1004Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487]
private theorem transition1004Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1004Input0) = fromList transition1004Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1004 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1147 = 2 • support0910 := by
  have hs : support1147 = fromList transition1004Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1004Chunk0]
  have hn : (transition1004Raw0 : Multiset ℕ) = 2 • (supportNumbers0910 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0910] using hm

private def transition1005Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 256, 258, 260, 262, 321, 323, 325, 327, 384, 386, 388, 390, 449, 451, 453, 455, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 800, 802, 804, 806, 865, 867, 869, 871, 928, 930, 932, 934, 993, 995, 997, 999]
private def transition1005Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935]
private theorem transition1005Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1005Input0) = fromList transition1005Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1005 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1147 = 2 • support0912 := by
  have hs : support1147 = fromList transition1005Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1005Chunk0]
  have hn : (transition1005Raw0 : Multiset ℕ) = 2 • (supportNumbers0912 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0912] using hm

private def transition1006Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591]
private def transition1006Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private theorem transition1006Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1006Input0) = fromList transition1006Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1006 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0134 = 1 • support0211 := by
  have hs : support0134 = fromList transition1006Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1006Chunk0]
  have hn : (transition1006Raw0 : Multiset ℕ) = 1 • (supportNumbers0211 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0211] using hm

private def transition1007Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591]
private def transition1007Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 264, 904, 266, 906, 268, 908, 270, 910, 329, 969, 331, 971, 333, 973, 335, 975]
private theorem transition1007Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1007Input0) = fromList transition1007Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1007 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0134 = 1 • support0212 := by
  have hs : support0134 = fromList transition1007Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1007Chunk0]
  have hn : (transition1007Raw0 : Multiset ℕ) = 1 • (supportNumbers0212 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0212] using hm

private def transition1008Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591]
private def transition1008Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private theorem transition1008Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1008Input0) = fromList transition1008Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1008 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0134 = 1 • support0211 := by
  have hs : support0134 = fromList transition1008Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1008Chunk0]
  have hn : (transition1008Raw0 : Multiset ℕ) = 1 • (supportNumbers0211 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0211] using hm

private def transition1009Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1009Raw0 : List ℕ := [0, 4, 65, 69, 10, 14, 75, 79]
private theorem transition1009Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1009Input0) = fromList transition1009Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1009 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0211 = 1 • support1148 := by
  have hs : support0211 = fromList transition1009Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1009Chunk0]
  have hn : (transition1009Raw0 : Multiset ℕ) = 1 • (supportNumbers1148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1148] using hm

private def transition1010Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335]
private def transition1010Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 584, 10, 588, 14, 521, 75, 525, 79]
private theorem transition1010Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1010Input0) = fromList transition1010Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1010 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0211 = 1 • support1150 := by
  have hs : support0211 = fromList transition1010Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1010Chunk0]
  have hn : (transition1010Raw0 : Multiset ℕ) = 1 • (supportNumbers1150 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1150] using hm

private def transition1011Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 520, 522, 524, 526, 585, 587, 589, 591]
private def transition1011Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 264, 808, 266, 810, 268, 812, 270, 814, 329, 873, 331, 875, 333, 877, 335, 879]
private theorem transition1011Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1011Input0) = fromList transition1011Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1011 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0134 = 1 • support1152 := by
  have hs : support0134 = fromList transition1011Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1011Chunk0]
  have hn : (transition1011Raw0 : Multiset ℕ) = 1 • (supportNumbers1152 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1152] using hm

private def transition1012Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 264, 266, 268, 270, 329, 331, 333, 335, 544, 546, 548, 550, 609, 611, 613, 615, 808, 810, 812, 814, 873, 875, 877, 879]
private def transition1012Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 8, 10, 12, 14, 73, 75, 77, 79, 288, 290, 292, 294, 353, 355, 357, 359, 296, 298, 300, 302, 361, 363, 365, 367]
private theorem transition1012Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1012Input0) = fromList transition1012Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1012 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1152 = 1 • support1153 := by
  have hs : support1152 = fromList transition1012Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1012Chunk0]
  have hn : (transition1012Raw0 : Multiset ℕ) = 1 • (supportNumbers1153 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1153] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
