import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0546Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 130, 131, 134, 135, 146, 147, 150, 151, 194, 195, 198, 199, 210, 211, 214, 215]
private def finish0546Raw0 : List ℕ := [0, 1, 16, 17, 64, 65, 80, 81, 130, 131, 146, 147, 194, 195, 210, 211]
private theorem finish0546Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0546Input0) = fromList finish0546Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0546 : finishSupport ⟨false, bits4 4⟩ support1460 = 1 • support1461 := by
  have hs : support1460 = fromList finish0546Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0546Chunk0]
  have hn : (finish0546Raw0 : Multiset ℕ) = 1 • (supportNumbers1461 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1461] using hm

private def finish0547Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 130, 131, 134, 135, 146, 147, 150, 151, 194, 195, 198, 199, 210, 211, 214, 215, 514, 515, 518, 519, 530, 531, 534, 535, 578, 579, 582, 583, 594, 595, 598, 599, 640, 641, 644, 645, 656, 657, 660, 661, 704, 705, 708, 709, 720, 721, 724, 725]
private def finish0547Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 130, 131, 134, 135, 146, 147, 150, 151, 194, 195, 198, 199, 210, 211, 214, 215, 2, 3, 6, 7, 18, 19, 22, 23, 66, 67, 70, 71, 82, 83, 86, 87, 128, 129, 132, 133, 144, 145, 148, 149, 192, 193, 196, 197, 208, 209, 212, 213]
private theorem finish0547Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0547Input0) = fromList finish0547Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0547 : finishSupport ⟨true, bits4 4⟩ support1462 = 1 • support0164 := by
  have hs : support1462 = fromList finish0547Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0547Chunk0]
  have hn : (finish0547Raw0 : Multiset ℕ) = 1 • (supportNumbers0164 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0164] using hm

private def finish0548Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0548Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 128, 129, 130, 131, 144, 145, 146, 147, 192, 193, 194, 195, 208, 209, 210, 211]
private theorem finish0548Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0548Input0) = fromList finish0548Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0548Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0548Raw1 : List ℕ := [36, 37, 38, 39, 52, 53, 54, 55, 100, 101, 102, 103, 116, 117, 118, 119, 164, 165, 166, 167, 180, 181, 182, 183, 228, 229, 230, 231, 244, 245, 246, 247]
private theorem finish0548Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0548Input1) = fromList finish0548Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0548 : finishSupport ⟨false, bits4 4⟩ support1464 = 1 • support1465 := by
  have hs : support1464 = fromList finish0548Input0 + fromList finish0548Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0548Chunk0, finish0548Chunk1]
  have hn : (finish0548Raw0 : Multiset ℕ) + (finish0548Raw1 : Multiset ℕ) = 1 • (supportNumbers1465 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1465] using hm

private def finish0549Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0549Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0549Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0549Input0) = fromList finish0549Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0549Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0549Raw1 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0549Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0549Input1) = fromList finish0549Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0549Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0549Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0549Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0549Input2) = fromList finish0549Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0549Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 816, 817, 818, 819, 820, 821, 822, 823, 864, 865, 866, 867, 868, 869, 870, 871, 880, 881, 882, 883, 884, 885, 886, 887, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0549Raw3 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 48, 49, 50, 51, 52, 53, 54, 55, 96, 97, 98, 99, 100, 101, 102, 103, 112, 113, 114, 115, 116, 117, 118, 119, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0549Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0549Input3) = fromList finish0549Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0549 : finishSupport ⟨true, bits4 4⟩ support1466 = 2 • support1467 := by
  have hs : support1466 = fromList finish0549Input0 + fromList finish0549Input1 + fromList finish0549Input2 + fromList finish0549Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0549Chunk0, finish0549Chunk1, finish0549Chunk2, finish0549Chunk3]
  have hn : (finish0549Raw0 : Multiset ℕ) + (finish0549Raw1 : Multiset ℕ) + (finish0549Raw2 : Multiset ℕ) + (finish0549Raw3 : Multiset ℕ) = 2 • (supportNumbers1467 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1467] using hm

private def finish0550Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0550Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 44, 45, 46, 47, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127]
private theorem finish0550Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0550Input0) = fromList finish0550Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0550 : finishSupport ⟨false, bits4 4⟩ support1469 = 1 • support1470 := by
  have hs : support1469 = fromList finish0550Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0550Chunk0]
  have hn : (finish0550Raw0 : Multiset ℕ) = 1 • (supportNumbers1470 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1470] using hm

private def finish0551Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383]
private def finish0551Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63, 104, 105, 106, 107, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125, 126, 127]
private theorem finish0551Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0551Input0) = fromList finish0551Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0551Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 808, 809, 810, 811, 812, 813, 814, 815, 824, 825, 826, 827, 828, 829, 830, 831, 872, 873, 874, 875, 876, 877, 878, 879, 888, 889, 890, 891, 892, 893, 894, 895]
private def finish0551Raw1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63, 104, 105, 106, 107, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125, 126, 127]
private theorem finish0551Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0551Input1) = fromList finish0551Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0551 : finishSupport ⟨true, bits4 4⟩ support1471 = 2 • support1472 := by
  have hs : support1471 = fromList finish0551Input0 + fromList finish0551Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0551Chunk0, finish0551Chunk1]
  have hn : (finish0551Raw0 : Multiset ℕ) + (finish0551Raw1 : Multiset ℕ) = 2 • (supportNumbers1472 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1472] using hm

private def finish0552Input0 : List ℕ := [0, 2, 136, 138, 296, 298, 416, 418]
private def finish0552Raw0 : List ℕ := [0, 2, 136, 138]
private theorem finish0552Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0552Input0) = fromList finish0552Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0552 : finishSupport ⟨false, bits4 4⟩ support1477 = 1 • support0053 := by
  have hs : support1477 = fromList finish0552Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0552Chunk0]
  have hn : (finish0552Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def finish0553Input0 : List ℕ := [0, 2, 136, 138, 296, 298, 416, 418, 576, 578, 712, 714, 872, 874, 992, 994]
private def finish0553Raw0 : List ℕ := [0, 2, 136, 138, 40, 42, 160, 162, 64, 66, 200, 202, 104, 106, 224, 226]
private theorem finish0553Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0553Input0) = fromList finish0553Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0553 : finishSupport ⟨true, bits4 4⟩ support1478 = 1 • support1479 := by
  have hs : support1478 = fromList finish0553Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0553Chunk0]
  have hn : (finish0553Raw0 : Multiset ℕ) = 1 • (supportNumbers1479 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1479] using hm

private def finish0554Input0 : List ℕ := [0, 10, 128, 138]
private def finish0554Raw0 : List ℕ := [0, 10, 128, 138]
private theorem finish0554Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0554Input0) = fromList finish0554Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0554 : finishSupport ⟨false, bits4 4⟩ support1480 = 1 • support1480 := by
  have hs : support1480 = fromList finish0554Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0554Chunk0]
  have hn : (finish0554Raw0 : Multiset ℕ) = 1 • (supportNumbers1480 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1480] using hm

private def finish0555Input0 : List ℕ := [0, 10, 128, 138, 578, 584, 706, 712]
private def finish0555Raw0 : List ℕ := [0, 10, 128, 138, 66, 72, 194, 200]
private theorem finish0555Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0555Input0) = fromList finish0555Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0555 : finishSupport ⟨true, bits4 4⟩ support1481 = 1 • support1482 := by
  have hs : support1481 = fromList finish0555Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0555Chunk0]
  have hn : (finish0555Raw0 : Multiset ℕ) = 1 • (supportNumbers1482 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1482] using hm

private def finish0556Input0 : List ℕ := [0, 139]
private def finish0556Raw0 : List ℕ := [0, 139]
private theorem finish0556Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0556Input0) = fromList finish0556Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0556 : finishSupport ⟨false, bits4 4⟩ support1484 = 1 • support1484 := by
  have hs : support1484 = fromList finish0556Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0556Chunk0]
  have hn : (finish0556Raw0 : Multiset ℕ) = 1 • (supportNumbers1484 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1484] using hm

private def finish0557Input0 : List ℕ := [0, 139, 578, 713]
private def finish0557Raw0 : List ℕ := [0, 139, 66, 201]
private theorem finish0557Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0557Input0) = fromList finish0557Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0557 : finishSupport ⟨true, bits4 4⟩ support1485 = 1 • support1486 := by
  have hs : support1485 = fromList finish0557Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0557Chunk0]
  have hn : (finish0557Raw0 : Multiset ℕ) = 1 • (supportNumbers1486 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1486] using hm

private def finish0558Input0 : List ℕ := [0, 2, 137, 139, 288, 290, 425, 427]
private def finish0558Raw0 : List ℕ := [0, 2, 137, 139]
private theorem finish0558Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0558Input0) = fromList finish0558Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0558 : finishSupport ⟨false, bits4 4⟩ support1488 = 1 • support0026 := by
  have hs : support1488 = fromList finish0558Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0558Chunk0]
  have hn : (finish0558Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def finish0559Input0 : List ℕ := [0, 2, 137, 139, 288, 290, 425, 427, 576, 578, 713, 715, 864, 866, 1001, 1003]
private def finish0559Raw0 : List ℕ := [0, 2, 137, 139, 32, 34, 169, 171, 64, 66, 201, 203, 96, 98, 233, 235]
private theorem finish0559Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0559Input0) = fromList finish0559Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0559 : finishSupport ⟨true, bits4 4⟩ support1489 = 1 • support1490 := by
  have hs : support1489 = fromList finish0559Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0559Chunk0]
  have hn : (finish0559Raw0 : Multiset ℕ) = 1 • (supportNumbers1490 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1490] using hm

private def finish0560Input0 : List ℕ := [0, 2, 137, 139]
private def finish0560Raw0 : List ℕ := [0, 2, 137, 139]
private theorem finish0560Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0560Input0) = fromList finish0560Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0560 : finishSupport ⟨false, bits4 4⟩ support0026 = 1 • support0026 := by
  have hs : support0026 = fromList finish0560Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0560Chunk0]
  have hn : (finish0560Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def finish0561Input0 : List ℕ := [0, 2, 137, 139, 576, 578, 713, 715]
private def finish0561Raw0 : List ℕ := [0, 2, 137, 139, 64, 66, 201, 203]
private theorem finish0561Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0561Input0) = fromList finish0561Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0561 : finishSupport ⟨true, bits4 4⟩ support1491 = 1 • support1492 := by
  have hs : support1491 = fromList finish0561Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0561Chunk0]
  have hn : (finish0561Raw0 : Multiset ℕ) = 1 • (supportNumbers1492 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1492] using hm

private def finish0562Input0 : List ℕ := [0, 9, 128, 137]
private def finish0562Raw0 : List ℕ := [0, 9, 128, 137]
private theorem finish0562Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0562Input0) = fromList finish0562Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0562 : finishSupport ⟨false, bits4 4⟩ support1494 = 1 • support1494 := by
  have hs : support1494 = fromList finish0562Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0562Chunk0]
  have hn : (finish0562Raw0 : Multiset ℕ) = 1 • (supportNumbers1494 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1494] using hm

private def finish0563Input0 : List ℕ := [0, 9, 128, 137, 578, 587, 706, 715]
private def finish0563Raw0 : List ℕ := [0, 9, 128, 137, 66, 75, 194, 203]
private theorem finish0563Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0563Input0) = fromList finish0563Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0563 : finishSupport ⟨true, bits4 4⟩ support1495 = 1 • support1496 := by
  have hs : support1495 = fromList finish0563Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0563Chunk0]
  have hn : (finish0563Raw0 : Multiset ℕ) = 1 • (supportNumbers1496 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1496] using hm

private def finish0564Input0 : List ℕ := [0, 3, 9, 10]
private def finish0564Raw0 : List ℕ := [0, 3, 9, 10]
private theorem finish0564Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0564Input0) = fromList finish0564Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0564 : finishSupport ⟨false, bits4 4⟩ support1498 = 1 • support1498 := by
  have hs : support1498 = fromList finish0564Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0564Chunk0]
  have hn : (finish0564Raw0 : Multiset ℕ) = 1 • (supportNumbers1498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1498] using hm

private def finish0565Input0 : List ℕ := [0, 3, 9, 10, 577, 578, 584, 587]
private def finish0565Raw0 : List ℕ := [0, 3, 9, 10, 65, 66, 72, 75]
private theorem finish0565Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0565Input0) = fromList finish0565Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0565 : finishSupport ⟨true, bits4 4⟩ support1499 = 1 • support1500 := by
  have hs : support1499 = fromList finish0565Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0565Chunk0]
  have hn : (finish0565Raw0 : Multiset ℕ) = 1 • (supportNumbers1500 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1500] using hm

private def finish0566Input0 : List ℕ := [0, 1, 138, 139]
private def finish0566Raw0 : List ℕ := [0, 1, 138, 139]
private theorem finish0566Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0566Input0) = fromList finish0566Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0566 : finishSupport ⟨false, bits4 4⟩ support0575 = 1 • support0575 := by
  have hs : support0575 = fromList finish0566Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0566Chunk0]
  have hn : (finish0566Raw0 : Multiset ℕ) = 1 • (supportNumbers0575 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0575] using hm

private def finish0567Input0 : List ℕ := [0, 1, 138, 139, 578, 579, 712, 713]
private def finish0567Raw0 : List ℕ := [0, 1, 138, 139, 66, 67, 200, 201]
private theorem finish0567Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0567Input0) = fromList finish0567Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0567 : finishSupport ⟨true, bits4 4⟩ support1502 = 1 • support1503 := by
  have hs : support1502 = fromList finish0567Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0567Chunk0]
  have hn : (finish0567Raw0 : Multiset ℕ) = 1 • (supportNumbers1503 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1503] using hm

private def finish0568Input0 : List ℕ := [0, 3, 129, 130]
private def finish0568Raw0 : List ℕ := [0, 3, 129, 130]
private theorem finish0568Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0568Input0) = fromList finish0568Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0568 : finishSupport ⟨false, bits4 4⟩ support1506 = 1 • support1506 := by
  have hs : support1506 = fromList finish0568Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0568Chunk0]
  have hn : (finish0568Raw0 : Multiset ℕ) = 1 • (supportNumbers1506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1506] using hm

private def finish0569Input0 : List ℕ := [0, 3, 129, 130, 577, 578, 704, 707]
private def finish0569Raw0 : List ℕ := [0, 3, 129, 130, 65, 66, 192, 195]
private theorem finish0569Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0569Input0) = fromList finish0569Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0569 : finishSupport ⟨true, bits4 4⟩ support1507 = 1 • support1508 := by
  have hs : support1507 = fromList finish0569Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0569Chunk0]
  have hn : (finish0569Raw0 : Multiset ℕ) = 1 • (supportNumbers1508 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1508] using hm

private def finish0570Input0 : List ℕ := [0, 2, 129, 131, 296, 298, 425, 427]
private def finish0570Raw0 : List ℕ := [0, 2, 129, 131]
private theorem finish0570Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0570Input0) = fromList finish0570Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0570 : finishSupport ⟨false, bits4 4⟩ support1511 = 1 • support0110 := by
  have hs : support1511 = fromList finish0570Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0570Chunk0]
  have hn : (finish0570Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def finish0571Input0 : List ℕ := [0, 2, 129, 131, 296, 298, 425, 427, 576, 578, 705, 707, 872, 874, 1001, 1003]
private def finish0571Raw0 : List ℕ := [0, 2, 129, 131, 40, 42, 169, 171, 64, 66, 193, 195, 104, 106, 233, 235]
private theorem finish0571Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0571Input0) = fromList finish0571Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0571 : finishSupport ⟨true, bits4 4⟩ support1512 = 1 • support1513 := by
  have hs : support1512 = fromList finish0571Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0571Chunk0]
  have hn : (finish0571Raw0 : Multiset ℕ) = 1 • (supportNumbers1513 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1513] using hm

private def finish0572Input0 : List ℕ := [0, 1, 28, 29, 130, 131, 158, 159]
private def finish0572Raw0 : List ℕ := [0, 1, 130, 131]
private theorem finish0572Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0572Input0) = fromList finish0572Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0572 : finishSupport ⟨false, bits4 4⟩ support1518 = 1 • support0857 := by
  have hs : support1518 = fromList finish0572Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0572Chunk0]
  have hn : (finish0572Raw0 : Multiset ℕ) = 1 • (supportNumbers0857 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0857] using hm

private def finish0573Input0 : List ℕ := [0, 1, 28, 29, 130, 131, 158, 159, 578, 579, 606, 607, 704, 705, 732, 733]
private def finish0573Raw0 : List ℕ := [0, 1, 28, 29, 130, 131, 158, 159, 66, 67, 94, 95, 192, 193, 220, 221]
private theorem finish0573Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0573Input0) = fromList finish0573Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0573 : finishSupport ⟨true, bits4 4⟩ support1519 = 1 • support1520 := by
  have hs : support1519 = fromList finish0573Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0573Chunk0]
  have hn : (finish0573Raw0 : Multiset ℕ) = 1 • (supportNumbers1520 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1520] using hm

private def finish0574Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 316, 317, 318, 319, 444, 445, 446, 447]
private def finish0574Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 60, 61, 62, 63, 188, 189, 190, 191]
private theorem finish0574Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0574Input0) = fromList finish0574Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0574 : finishSupport ⟨false, bits4 4⟩ support1524 = 1 • support0862 := by
  have hs : support1524 = fromList finish0574Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0574Chunk0]
  have hn : (finish0574Raw0 : Multiset ℕ) = 1 • (supportNumbers0862 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0862] using hm

private def finish0575Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 316, 317, 318, 319, 444, 445, 446, 447, 576, 577, 578, 579, 704, 705, 706, 707, 892, 893, 894, 895, 1020, 1021, 1022, 1023]
private def finish0575Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 60, 61, 62, 63, 188, 189, 190, 191, 64, 65, 66, 67, 192, 193, 194, 195, 124, 125, 126, 127, 252, 253, 254, 255]
private theorem finish0575Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0575Input0) = fromList finish0575Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0575 : finishSupport ⟨true, bits4 4⟩ support1525 = 1 • support1526 := by
  have hs : support1525 = fromList finish0575Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0575Chunk0]
  have hn : (finish0575Raw0 : Multiset ℕ) = 1 • (supportNumbers1526 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1526] using hm

private def finish0576Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 296, 297, 298, 299, 416, 417, 418, 419]
private def finish0576Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem finish0576Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0576Input0) = fromList finish0576Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0576 : finishSupport ⟨false, bits4 4⟩ support1528 = 1 • support0065 := by
  have hs : support1528 = fromList finish0576Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0576Chunk0]
  have hn : (finish0576Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def finish0577Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 296, 297, 298, 299, 416, 417, 418, 419, 576, 577, 578, 579, 712, 713, 714, 715, 872, 873, 874, 875, 992, 993, 994, 995]
private def finish0577Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 40, 41, 42, 43, 160, 161, 162, 163, 64, 65, 66, 67, 200, 201, 202, 203, 104, 105, 106, 107, 224, 225, 226, 227]
private theorem finish0577Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0577Input0) = fromList finish0577Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0577 : finishSupport ⟨true, bits4 4⟩ support1529 = 1 • support1530 := by
  have hs : support1529 = fromList finish0577Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0577Chunk0]
  have hn : (finish0577Raw0 : Multiset ℕ) = 1 • (supportNumbers1530 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1530] using hm

private def finish0578Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 436, 437, 438, 439, 444, 445, 446, 447]
private def finish0578Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 180, 181, 182, 183, 188, 189, 190, 191]
private theorem finish0578Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0578Input0) = fromList finish0578Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0578 : finishSupport ⟨false, bits4 4⟩ support1532 = 1 • support1117 := by
  have hs : support1532 = fromList finish0578Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0578Chunk0]
  have hn : (finish0578Raw0 : Multiset ℕ) = 1 • (supportNumbers1117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1117] using hm

private def finish0579Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 436, 437, 438, 439, 444, 445, 446, 447, 576, 577, 578, 579, 584, 585, 586, 587, 1012, 1013, 1014, 1015, 1020, 1021, 1022, 1023]
private def finish0579Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 180, 181, 182, 183, 188, 189, 190, 191, 64, 65, 66, 67, 72, 73, 74, 75, 244, 245, 246, 247, 252, 253, 254, 255]
private theorem finish0579Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0579Input0) = fromList finish0579Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0579 : finishSupport ⟨true, bits4 4⟩ support1533 = 1 • support1534 := by
  have hs : support1533 = fromList finish0579Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0579Chunk0]
  have hn : (finish0579Raw0 : Multiset ℕ) = 1 • (supportNumbers1534 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1534] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
