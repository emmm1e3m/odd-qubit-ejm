import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0079Input0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215, 514, 515, 518, 519, 538, 539, 542, 543, 578, 579, 582, 583, 602, 603, 606, 607, 648, 649, 652, 653, 656, 657, 660, 661, 712, 713, 716, 717, 720, 721, 724, 725]
private def finish0079Raw0 : List ℕ := [0, 1, 4, 5, 24, 25, 28, 29, 64, 65, 68, 69, 88, 89, 92, 93, 138, 139, 142, 143, 146, 147, 150, 151, 202, 203, 206, 207, 210, 211, 214, 215, 2, 3, 6, 7, 26, 27, 30, 31, 66, 67, 70, 71, 90, 91, 94, 95, 136, 137, 140, 141, 144, 145, 148, 149, 200, 201, 204, 205, 208, 209, 212, 213]
private theorem finish0079Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0079Input0) = fromList finish0079Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0079 : finishSupport ⟨true, bits4 4⟩ support0628 = 1 • support0411 := by
  have hs : support0628 = fromList finish0079Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0079Chunk0]
  have hn : (finish0079Raw0 : Multiset ℕ) = 1 • (supportNumbers0411 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0411] using hm

private def finish0080Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0080Raw0 : List ℕ := [0, 1, 2, 3, 24, 25, 26, 27, 64, 65, 66, 67, 88, 89, 90, 91, 136, 137, 138, 139, 144, 145, 146, 147, 200, 201, 202, 203, 208, 209, 210, 211]
private theorem finish0080Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0080Input0) = fromList finish0080Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0080Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0080Raw1 : List ℕ := [36, 37, 38, 39, 60, 61, 62, 63, 100, 101, 102, 103, 124, 125, 126, 127, 172, 173, 174, 175, 180, 181, 182, 183, 236, 237, 238, 239, 244, 245, 246, 247]
private theorem finish0080Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0080Input1) = fromList finish0080Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0080 : finishSupport ⟨false, bits4 4⟩ support0630 = 1 • support0631 := by
  have hs : support0630 = fromList finish0080Input0 + fromList finish0080Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0080Chunk0, finish0080Chunk1]
  have hn : (finish0080Raw0 : Multiset ℕ) + (finish0080Raw1 : Multiset ℕ) = 1 • (supportNumbers0631 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0631] using hm

private def finish0081Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private def finish0081Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0081Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0081Input0) = fromList finish0081Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0081Input1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 312, 313, 314, 315, 316, 317, 318, 319, 352, 353, 354, 355, 356, 357, 358, 359, 376, 377, 378, 379, 380, 381, 382, 383, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0081Raw1 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0081Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0081Input1) = fromList finish0081Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0081Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 536, 537, 538, 539, 540, 541, 542, 543, 576, 577, 578, 579, 580, 581, 582, 583, 600, 601, 602, 603, 604, 605, 606, 607, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727]
private def finish0081Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem finish0081Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0081Input2) = fromList finish0081Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0081Input3 : List ℕ := [800, 801, 802, 803, 804, 805, 806, 807, 824, 825, 826, 827, 828, 829, 830, 831, 864, 865, 866, 867, 868, 869, 870, 871, 888, 889, 890, 891, 892, 893, 894, 895, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0081Raw3 : List ℕ := [32, 33, 34, 35, 36, 37, 38, 39, 56, 57, 58, 59, 60, 61, 62, 63, 96, 97, 98, 99, 100, 101, 102, 103, 120, 121, 122, 123, 124, 125, 126, 127, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0081Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0081Input3) = fromList finish0081Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0081 : finishSupport ⟨true, bits4 4⟩ support0632 = 2 • support0633 := by
  have hs : support0632 = fromList finish0081Input0 + fromList finish0081Input1 + fromList finish0081Input2 + fromList finish0081Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0081Chunk0, finish0081Chunk1, finish0081Chunk2, finish0081Chunk3]
  have hn : (finish0081Raw0 : Multiset ℕ) + (finish0081Raw1 : Multiset ℕ) + (finish0081Raw2 : Multiset ℕ) + (finish0081Raw3 : Multiset ℕ) = 2 • (supportNumbers0633 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0633] using hm

private def finish0082Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221]
private def finish0082Raw0 : List ℕ := [0, 1, 16, 17, 64, 65, 80, 81, 136, 137, 152, 153, 200, 201, 216, 217]
private theorem finish0082Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0082Input0) = fromList finish0082Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0082 : finishSupport ⟨false, bits4 4⟩ support0634 = 1 • support0635 := by
  have hs : support0634 = fromList finish0082Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0082Chunk0]
  have hn : (finish0082Raw0 : Multiset ℕ) = 1 • (supportNumbers0635 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0635] using hm

private def finish0083Input0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221, 514, 515, 518, 519, 530, 531, 534, 535, 578, 579, 582, 583, 594, 595, 598, 599, 650, 651, 654, 655, 666, 667, 670, 671, 714, 715, 718, 719, 730, 731, 734, 735]
private def finish0083Raw0 : List ℕ := [0, 1, 4, 5, 16, 17, 20, 21, 64, 65, 68, 69, 80, 81, 84, 85, 136, 137, 140, 141, 152, 153, 156, 157, 200, 201, 204, 205, 216, 217, 220, 221, 2, 3, 6, 7, 18, 19, 22, 23, 66, 67, 70, 71, 82, 83, 86, 87, 138, 139, 142, 143, 154, 155, 158, 159, 202, 203, 206, 207, 218, 219, 222, 223]
private theorem finish0083Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0083Input0) = fromList finish0083Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0083 : finishSupport ⟨true, bits4 4⟩ support0636 = 1 • support0048 := by
  have hs : support0636 = fromList finish0083Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0083Chunk0]
  have hn : (finish0083Raw0 : Multiset ℕ) = 1 • (supportNumbers0048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0048] using hm

private def finish0084Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0084Raw0 : List ℕ := [0, 1, 2, 3, 16, 17, 18, 19, 64, 65, 66, 67, 80, 81, 82, 83, 136, 137, 138, 139, 152, 153, 154, 155, 200, 201, 202, 203, 216, 217, 218, 219]
private theorem finish0084Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0084Input0) = fromList finish0084Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0084Input1 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0084Raw1 : List ℕ := [44, 45, 46, 47, 60, 61, 62, 63, 108, 109, 110, 111, 124, 125, 126, 127, 164, 165, 166, 167, 180, 181, 182, 183, 228, 229, 230, 231, 244, 245, 246, 247]
private theorem finish0084Chunk1 : finishSupport ⟨false, bits4 4⟩ (fromList finish0084Input1) = fromList finish0084Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0084 : finishSupport ⟨false, bits4 4⟩ support0638 = 1 • support0639 := by
  have hs : support0638 = fromList finish0084Input0 + fromList finish0084Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0084Chunk0, finish0084Chunk1]
  have hn : (finish0084Raw0 : Multiset ℕ) + (finish0084Raw1 : Multiset ℕ) = 1 • (supportNumbers0639 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0639] using hm

private def finish0085Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private def finish0085Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0085Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0085Input0) = fromList finish0085Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0085Input1 : List ℕ := [296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private def finish0085Raw1 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63, 104, 105, 106, 107, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0085Chunk1 : finishSupport ⟨true, bits4 4⟩ (fromList finish0085Input1) = fromList finish0085Raw1 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0085Input2 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 528, 529, 530, 531, 532, 533, 534, 535, 576, 577, 578, 579, 580, 581, 582, 583, 592, 593, 594, 595, 596, 597, 598, 599, 648, 649, 650, 651, 652, 653, 654, 655, 664, 665, 666, 667, 668, 669, 670, 671, 712, 713, 714, 715, 716, 717, 718, 719, 728, 729, 730, 731, 732, 733, 734, 735]
private def finish0085Raw2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 136, 137, 138, 139, 140, 141, 142, 143, 152, 153, 154, 155, 156, 157, 158, 159, 200, 201, 202, 203, 204, 205, 206, 207, 216, 217, 218, 219, 220, 221, 222, 223]
private theorem finish0085Chunk2 : finishSupport ⟨true, bits4 4⟩ (fromList finish0085Input2) = fromList finish0085Raw2 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def finish0085Input3 : List ℕ := [808, 809, 810, 811, 812, 813, 814, 815, 824, 825, 826, 827, 828, 829, 830, 831, 872, 873, 874, 875, 876, 877, 878, 879, 888, 889, 890, 891, 892, 893, 894, 895, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def finish0085Raw3 : List ℕ := [40, 41, 42, 43, 44, 45, 46, 47, 56, 57, 58, 59, 60, 61, 62, 63, 104, 105, 106, 107, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125, 126, 127, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179, 180, 181, 182, 183, 224, 225, 226, 227, 228, 229, 230, 231, 240, 241, 242, 243, 244, 245, 246, 247]
private theorem finish0085Chunk3 : finishSupport ⟨true, bits4 4⟩ (fromList finish0085Input3) = fromList finish0085Raw3 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0085 : finishSupport ⟨true, bits4 4⟩ support0640 = 2 • support0641 := by
  have hs : support0640 = fromList finish0085Input0 + fromList finish0085Input1 + fromList finish0085Input2 + fromList finish0085Input3 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0085Chunk0, finish0085Chunk1, finish0085Chunk2, finish0085Chunk3]
  have hn : (finish0085Raw0 : Multiset ℕ) + (finish0085Raw1 : Multiset ℕ) + (finish0085Raw2 : Multiset ℕ) + (finish0085Raw3 : Multiset ℕ) = 2 • (supportNumbers0641 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0641] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
