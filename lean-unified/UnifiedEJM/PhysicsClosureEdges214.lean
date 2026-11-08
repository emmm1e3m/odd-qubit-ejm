import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0625Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0625Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0625Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0625Input0) = fromList finish0625Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0625Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0625Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0625Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0625Input1) = fromList finish0625Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0625 : finishSupport ⟨true, bits4 4⟩ support0412 = 2 • support0411 := by
  have hs : support0412 = fromList finish0625Input0 + fromList finish0625Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0625Chunk0, finish0625Chunk1]
  have hn : (finish0625Raw0 : Multiset ℕ) + (finish0625Raw1 : Multiset ℕ) = 2 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def finish0626Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0626Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 136, 137, 138, 139, 144, 145, 146, 147, 200, 201, 202, 203, 208, 209, 210, 211]
private theorem finish0626Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0626Input0) = fromList finish0626Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0626Input1 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0626Raw1 : List ℕ := [44, 45, 46, 47, 52, 53, 54, 55, 108, 109, 110, 111, 116, 117, 118, 119, 164, 165, 166, 167, 188, 189, 190, 191, 228, 229, 230, 231, 252, 253, 254, 255]
private theorem finish0626Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0626Input1) = fromList finish0626Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0626 : finishSupport ⟨false, bits4 4⟩ support1624 = 1 • support1625 := by
  have hs : support1624 = fromList finish0626Input0 + fromList finish0626Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0626Chunk0, finish0626Chunk1]
  have hn : (finish0626Raw0 : Multiset ℕ) + (finish0626Raw1 : Multiset ℕ) = 1 • (supportNumbers1625 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1625] using hm

private def finish0627Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0627Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0627Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0627Input0) = fromList finish0627Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0627Input1 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 440, 441, 442, 443, 444, 445, 446, 447, 480, 481, 482, 483, 484, 485, 486, 487, 504, 505, 506, 507, 508, 509, 510, 511]
private def finish0627Raw1 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0627Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0627Input1) = fromList finish0627Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0627Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0627Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0627Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0627Input2) = fromList finish0627Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0627Input3 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 928, 929, 930, 931, 932, 933, 934, 935, 952, 953, 954, 955, 956, 957, 958, 959, 992, 993, 994, 995, 996, 997, 998, 999, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def finish0627Raw3 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 184, 185, 186, 187, 188, 189, 190, 191, 224, 225, 226, 227, 228, 229, 230, 231, 248, 249, 250, 251, 252, 253, 254, 255]
private theorem finish0627Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0627Input3) = fromList finish0627Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0627 : finishSupport ⟨true, bits4 4⟩ support1626 = 2 • support1627 := by
  have hs : support1626 = fromList finish0627Input0 + fromList finish0627Input1 + fromList finish0627Input2 + fromList finish0627Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0627Chunk0, finish0627Chunk1, finish0627Chunk2, finish0627Chunk3]
  have hn : (finish0627Raw0 : Multiset ℕ) + (finish0627Raw1 : Multiset ℕ) + (finish0627Raw2 : Multiset ℕ) + (finish0627Raw3 : Multiset ℕ) = 2 • (supportNumbers1627 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1627] using hm

private def finish0628Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0628Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 164, 165, 166, 167, 180, 181, 182, 183, 228, 229, 230, 231, 244, 245, 246, 247]
private theorem finish0628Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0628Input0) = fromList finish0628Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0628 : finishSupport ⟨false, bits4 4⟩ support1629 = 1 • support1630 := by
  have hs : support1629 = fromList finish0628Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0628Chunk0]
  have hn : (finish0628Raw0 : Multiset ℕ) = 1 • (supportNumbers1630 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1630] using hm

private def finish0629Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0629Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0629Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0629Input0) = fromList finish0629Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0629Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0629Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0629Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0629Input1) = fromList finish0629Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0629 : finishSupport ⟨true, bits4 4⟩ support1631 = 2 • support1632 := by
  have hs : support1631 = fromList finish0629Input0 + fromList finish0629Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0629Chunk0, finish0629Chunk1]
  have hn : (finish0629Raw0 : Multiset ℕ) + (finish0629Raw1 : Multiset ℕ) = 2 • (supportNumbers1632 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1632] using hm

private def finish0630Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 138, 139, 142, 143, 154, 155, 158, 159, 202, 203, 206, 207, 218, 219, 222, 223]
private def finish0630Raw0 : List ℕ := [0, 1, 16, 17, 64, 65, 80, 81, 138, 139, 154, 155, 202, 203, 218, 219]
private theorem finish0630Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0630Input0) = fromList finish0630Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0630 : finishSupport ⟨false, bits4 4⟩ support1634 = 1 • support1635 := by
  have hs : support1634 = fromList finish0630Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0630Chunk0]
  have hn : (finish0630Raw0 : Multiset ℕ) = 1 • (supportNumbers1635 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1635] using hm

private def finish0631Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 138, 139, 142, 143, 154, 155, 158, 159, 202, 203, 206, 207, 218, 219, 222, 223, 514, 515, 518, 519, 530, 531, 534, 535, 578, 579, 582, 583, 594, 595, 598, 599, 648, 649, 652, 653, 664, 665, 668, 669, 712, 713, 716, 717, 728, 729, 732, 733]
private def finish0631Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 138, 139, 142, 143, 154, 155, 158, 159, 202, 203, 206, 207, 218, 219, 222, 223, 2, 3, 6, 7, 18, 19, 22, 23, 66, 67, 70, 71, 82, 83, 86, 87, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221]
private theorem finish0631Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0631Input0) = fromList finish0631Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0631 : finishSupport ⟨true, bits4 4⟩ support1636 = 1 • support0048 := by
  have hs : support1636 = fromList finish0631Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0631Chunk0]
  have hn : (finish0631Raw0 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def finish0632Input0 : List ℕ := [0, 11, 130, 137]
private def finish0632Raw0 : List ℕ := [0, 11, 130, 137]
private theorem finish0632Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0632Input0) = fromList finish0632Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0632 : finishSupport ⟨false, bits4 4⟩ support1639 = 1 • support1639 := by
  have hs : support1639 = fromList finish0632Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0632Chunk0]
  have hn : (finish0632Raw0 : Multiset ℕ) = 1 • (supportNumbers1639 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1639] using hm

private def finish0633Input0 : List ℕ := [0, 11, 130, 137, 578, 585, 704, 715]
private def finish0633Raw0 : List ℕ := [0, 11, 130, 137, 66, 73, 192, 203]
private theorem finish0633Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0633Input0) = fromList finish0633Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0633 : finishSupport ⟨true, bits4 4⟩ support1640 = 1 • support1641 := by
  have hs : support1640 = fromList finish0633Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0633Chunk0]
  have hn : (finish0633Raw0 : Multiset ℕ) = 1 • (supportNumbers1641 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1641] using hm

private def finish0634Input0 : List ℕ := [0, 2, 128, 130, 297, 299, 425, 427]
private def finish0634Raw0 : List ℕ := [0, 2, 128, 130]
private theorem finish0634Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0634Input0) = fromList finish0634Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0634 : finishSupport ⟨false, bits4 4⟩ support1647 = 1 • support0252 := by
  have hs : support1647 = fromList finish0634Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0634Chunk0]
  have hn : (finish0634Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def finish0635Input0 : List ℕ := [0, 2, 128, 130, 297, 299, 425, 427, 576, 578, 704, 706, 873, 875, 1001, 1003]
private def finish0635Raw0 : List ℕ := [0, 2, 128, 130, 41, 43, 169, 171, 64, 66, 192, 194, 105, 107, 233, 235]
private theorem finish0635Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0635Input0) = fromList finish0635Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0635 : finishSupport ⟨true, bits4 4⟩ support1648 = 1 • support1649 := by
  have hs : support1648 = fromList finish0635Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0635Chunk0]
  have hn : (finish0635Raw0 : Multiset ℕ) = 1 • (supportNumbers1649 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1649] using hm

private def finish0636Input0 : List ℕ := [0, 2, 8, 10, 289, 291, 297, 299]
private def finish0636Raw0 : List ℕ := [0, 2, 8, 10]
private theorem finish0636Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0636Input0) = fromList finish0636Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0636 : finishSupport ⟨false, bits4 4⟩ support1651 = 1 • support0000 := by
  have hs : support1651 = fromList finish0636Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0636Chunk0]
  have hn : (finish0636Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def finish0637Input0 : List ℕ := [0, 2, 8, 10, 289, 291, 297, 299, 576, 578, 584, 586, 865, 867, 873, 875]
private def finish0637Raw0 : List ℕ := [0, 2, 8, 10, 33, 35, 41, 43, 64, 66, 72, 74, 97, 99, 105, 107]
private theorem finish0637Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0637Input0) = fromList finish0637Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0637 : finishSupport ⟨true, bits4 4⟩ support1652 = 1 • support1653 := by
  have hs : support1652 = fromList finish0637Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0637Chunk0]
  have hn : (finish0637Raw0 : Multiset ℕ) = 1 • (supportNumbers1653 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1653] using hm

private def finish0638Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def finish0638Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem finish0638Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0638Input0) = fromList finish0638Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0638 : finishSupport ⟨false, bits4 4⟩ support0065 = 1 • support0065 := by
  have hs : support0065 = fromList finish0638Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0638Chunk0]
  have hn : (finish0638Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def finish0639Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 576, 577, 578, 579, 712, 713, 714, 715]
private def finish0639Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 64, 65, 66, 67, 200, 201, 202, 203]
private theorem finish0639Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0639Input0) = fromList finish0639Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0639 : finishSupport ⟨true, bits4 4⟩ support1654 = 1 • support1655 := by
  have hs : support1654 = fromList finish0639Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0639Chunk0]
  have hn : (finish0639Raw0 : Multiset ℕ) = 1 • (supportNumbers1655 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1655] using hm

private def finish0640Input0 : List ℕ := [0, 2, 129, 131, 289, 291, 416, 418]
private def finish0640Raw0 : List ℕ := [0, 2, 129, 131]
private theorem finish0640Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0640Input0) = fromList finish0640Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0640 : finishSupport ⟨false, bits4 4⟩ support1658 = 1 • support0110 := by
  have hs : support1658 = fromList finish0640Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0640Chunk0]
  have hn : (finish0640Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def finish0641Input0 : List ℕ := [0, 2, 129, 131, 289, 291, 416, 418, 576, 578, 705, 707, 865, 867, 992, 994]
private def finish0641Raw0 : List ℕ := [0, 2, 129, 131, 33, 35, 160, 162, 64, 66, 193, 195, 97, 99, 224, 226]
private theorem finish0641Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0641Input0) = fromList finish0641Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0641 : finishSupport ⟨true, bits4 4⟩ support1659 = 1 • support1660 := by
  have hs : support1659 = fromList finish0641Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0641Chunk0]
  have hn : (finish0641Raw0 : Multiset ℕ) = 1 • (supportNumbers1660 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1660] using hm

private def finish0642Input0 : List ℕ := [0, 11, 129, 138]
private def finish0642Raw0 : List ℕ := [0, 11, 129, 138]
private theorem finish0642Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0642Input0) = fromList finish0642Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0642 : finishSupport ⟨false, bits4 4⟩ support1661 = 1 • support1661 := by
  have hs : support1661 = fromList finish0642Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0642Chunk0]
  have hn : (finish0642Raw0 : Multiset ℕ) = 1 • (supportNumbers1661 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1661] using hm

private def finish0643Input0 : List ℕ := [0, 11, 129, 138, 578, 585, 707, 712]
private def finish0643Raw0 : List ℕ := [0, 11, 129, 138, 66, 73, 195, 200]
private theorem finish0643Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0643Input0) = fromList finish0643Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0643 : finishSupport ⟨true, bits4 4⟩ support1662 = 1 • support1663 := by
  have hs : support1662 = fromList finish0643Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0643Chunk0]
  have hn : (finish0643Raw0 : Multiset ℕ) = 1 • (supportNumbers1663 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1663] using hm

private def finish0644Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 316, 317, 318, 319, 416, 417, 418, 419]
private def finish0644Raw0 : List ℕ := [0, 1, 2, 3, 60, 61, 62, 63]
private theorem finish0644Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0644Input0) = fromList finish0644Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0644 : finishSupport ⟨false, bits4 4⟩ support1666 = 1 • support0571 := by
  have hs : support1666 = fromList finish0644Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0644Chunk0]
  have hn : (finish0644Raw0 : Multiset ℕ) = 1 • (supportNumbers0571 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0571] using hm

private def finish0645Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 316, 317, 318, 319, 416, 417, 418, 419, 576, 577, 578, 579, 732, 733, 734, 735, 892, 893, 894, 895, 992, 993, 994, 995]
private def finish0645Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 60, 61, 62, 63, 160, 161, 162, 163, 64, 65, 66, 67, 220, 221, 222, 223, 124, 125, 126, 127, 224, 225, 226, 227]
private theorem finish0645Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0645Input0) = fromList finish0645Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0645 : finishSupport ⟨true, bits4 4⟩ support1667 = 1 • support1668 := by
  have hs : support1667 = fromList finish0645Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0645Chunk0]
  have hn : (finish0645Raw0 : Multiset ℕ) = 1 • (supportNumbers1668 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1668] using hm

private def finish0646Input0 : List ℕ := [0, 1, 30, 31, 128, 129, 158, 159]
private def finish0646Raw0 : List ℕ := [0, 1, 128, 129]
private theorem finish0646Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0646Input0) = fromList finish0646Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0646 : finishSupport ⟨false, bits4 4⟩ support1669 = 1 • support0898 := by
  have hs : support1669 = fromList finish0646Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0646Chunk0]
  have hn : (finish0646Raw0 : Multiset ℕ) = 1 • (supportNumbers0898 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0898] using hm

private def finish0647Input0 : List ℕ := [0, 1, 30, 31, 128, 129, 158, 159, 578, 579, 604, 605, 706, 707, 732, 733]
private def finish0647Raw0 : List ℕ := [0, 1, 30, 31, 128, 129, 158, 159, 66, 67, 92, 93, 194, 195, 220, 221]
private theorem finish0647Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0647Input0) = fromList finish0647Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0647 : finishSupport ⟨true, bits4 4⟩ support1670 = 1 • support1671 := by
  have hs : support1670 = fromList finish0647Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0647Chunk0]
  have hn : (finish0647Raw0 : Multiset ℕ) = 1 • (supportNumbers1671 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1671] using hm

private def finish0648Input0 : List ℕ := [0, 1, 8, 9, 22, 23, 30, 31]
private def finish0648Raw0 : List ℕ := [0, 1, 8, 9]
private theorem finish0648Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0648Input0) = fromList finish0648Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0648 : finishSupport ⟨false, bits4 4⟩ support1674 = 1 • support0874 := by
  have hs : support1674 = fromList finish0648Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0648Chunk0]
  have hn : (finish0648Raw0 : Multiset ℕ) = 1 • (supportNumbers0874 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0874] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
