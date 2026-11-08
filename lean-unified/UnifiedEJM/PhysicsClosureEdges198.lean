import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def finish0239Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487, 513, 515, 517, 519, 576, 578, 580, 582, 641, 643, 645, 647, 704, 706, 708, 710, 801, 803, 805, 807, 864, 866, 868, 870, 929, 931, 933, 935, 992, 994, 996, 998]
private def finish0239Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 32, 34, 36, 38, 97, 99, 101, 103, 160, 162, 164, 166, 225, 227, 229, 231, 1, 3, 5, 7, 64, 66, 68, 70, 129, 131, 133, 135, 192, 194, 196, 198, 33, 35, 37, 39, 96, 98, 100, 102, 161, 163, 165, 167, 224, 226, 228, 230]
private theorem finish0239Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0239Input0) = fromList finish0239Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0239 : finishSupport ⟨true, bits4 4⟩ support0912 = 1 • support0913 := by
  have hs : support0912 = fromList finish0239Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0239Chunk0]
  have hn : (finish0239Raw0 : Multiset ℕ) = 1 • (supportNumbers0913 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0913] using hm

private def finish0240Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 424, 426, 428, 430, 489, 491, 493, 495]
private def finish0240Raw0 : List ℕ := [0, 2, 65, 67, 172, 174, 237, 239]
private theorem finish0240Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0240Input0) = fromList finish0240Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0240 : finishSupport ⟨false, bits4 4⟩ support0915 = 1 • support0916 := by
  have hs : support0915 = fromList finish0240Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0240Chunk0]
  have hn : (finish0240Raw0 : Multiset ℕ) = 1 • (supportNumbers0916 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0916] using hm

private def finish0241Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 424, 426, 428, 430, 489, 491, 493, 495, 513, 515, 517, 519, 576, 578, 580, 582, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def finish0241Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 168, 170, 172, 174, 233, 235, 237, 239, 1, 3, 5, 7, 64, 66, 68, 70, 169, 171, 173, 175, 232, 234, 236, 238]
private theorem finish0241Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0241Input0) = fromList finish0241Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0241 : finishSupport ⟨true, bits4 4⟩ support0917 = 1 • support0744 := by
  have hs : support0917 = fromList finish0241Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0241Chunk0]
  have hn : (finish0241Raw0 : Multiset ℕ) = 1 • (supportNumbers0744 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0744] using hm

private def finish0242Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77]
private def finish0242Raw0 : List ℕ := [0, 8, 65, 73]
private theorem finish0242Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0242Input0) = fromList finish0242Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0242 : finishSupport ⟨false, bits4 4⟩ support0919 = 1 • support0920 := by
  have hs : support0919 = fromList finish0242Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0242Chunk0]
  have hn : (finish0242Raw0 : Multiset ℕ) = 1 • (supportNumbers0920 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0920] using hm

private def finish0243Input0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 515, 519, 523, 527, 578, 582, 586, 590]
private def finish0243Raw0 : List ℕ := [0, 4, 8, 12, 65, 69, 73, 77, 3, 7, 11, 15, 66, 70, 74, 78]
private theorem finish0243Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0243Input0) = fromList finish0243Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0243 : finishSupport ⟨true, bits4 4⟩ support0921 = 1 • support0922 := by
  have hs : support0921 = fromList finish0243Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0243Chunk0]
  have hn : (finish0243Raw0 : Multiset ℕ) = 1 • (supportNumbers0922 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0922] using hm

private def finish0244Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495]
private def finish0244Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 164, 166, 172, 174, 229, 231, 237, 239]
private theorem finish0244Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0244Input0) = fromList finish0244Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0244 : finishSupport ⟨false, bits4 4⟩ support0924 = 1 • support0925 := by
  have hs : support0924 = fromList finish0244Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0244Chunk0]
  have hn : (finish0244Raw0 : Multiset ℕ) = 1 • (supportNumbers0925 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0925] using hm

private def finish0245Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 416, 418, 420, 422, 424, 426, 428, 430, 481, 483, 485, 487, 489, 491, 493, 495, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 929, 931, 933, 935, 937, 939, 941, 943, 992, 994, 996, 998, 1000, 1002, 1004, 1006]
private def finish0245Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 160, 162, 164, 166, 168, 170, 172, 174, 225, 227, 229, 231, 233, 235, 237, 239, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 161, 163, 165, 167, 169, 171, 173, 175, 224, 226, 228, 230, 232, 234, 236, 238]
private theorem finish0245Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0245Input0) = fromList finish0245Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0245 : finishSupport ⟨true, bits4 4⟩ support0926 = 1 • support0927 := by
  have hs : support0926 = fromList finish0245Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0245Chunk0]
  have hn : (finish0245Raw0 : Multiset ℕ) = 1 • (supportNumbers0927 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0927] using hm

private def finish0246Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207]
private def finish0246Raw0 : List ℕ := [0, 2, 8, 10, 65, 67, 73, 75, 128, 130, 136, 138, 193, 195, 201, 203]
private theorem finish0246Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0246Input0) = fromList finish0246Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0246 : finishSupport ⟨false, bits4 4⟩ support0215 = 1 • support0928 := by
  have hs : support0215 = fromList finish0246Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0246Chunk0]
  have hn : (finish0246Raw0 : Multiset ℕ) = 1 • (supportNumbers0928 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0928] using hm

private def finish0247Input0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 513, 515, 517, 519, 521, 523, 525, 527, 576, 578, 580, 582, 584, 586, 588, 590, 641, 643, 645, 647, 649, 651, 653, 655, 704, 706, 708, 710, 712, 714, 716, 718]
private def finish0247Raw0 : List ℕ := [0, 2, 4, 6, 8, 10, 12, 14, 65, 67, 69, 71, 73, 75, 77, 79, 128, 130, 132, 134, 136, 138, 140, 142, 193, 195, 197, 199, 201, 203, 205, 207, 1, 3, 5, 7, 9, 11, 13, 15, 64, 66, 68, 70, 72, 74, 76, 78, 129, 131, 133, 135, 137, 139, 141, 143, 192, 194, 196, 198, 200, 202, 204, 206]
private theorem finish0247Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0247Input0) = fromList finish0247Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0247 : finishSupport ⟨true, bits4 4⟩ support0929 = 1 • support0148 := by
  have hs : support0929 = fromList finish0247Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0247Chunk0]
  have hn : (finish0247Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0248Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78]
private def finish0248Raw0 : List ℕ := [0, 11, 65, 74]
private theorem finish0248Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0248Input0) = fromList finish0248Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0248 : finishSupport ⟨false, bits4 4⟩ support0931 = 1 • support0932 := by
  have hs : support0931 = fromList finish0248Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0248Chunk0]
  have hn : (finish0248Raw0 : Multiset ℕ) = 1 • (supportNumbers0932 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0932] using hm

private def finish0249Input0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 515, 519, 520, 524, 578, 582, 585, 589]
private def finish0249Raw0 : List ℕ := [0, 4, 11, 15, 65, 69, 74, 78, 3, 7, 8, 12, 66, 70, 73, 77]
private theorem finish0249Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0249Input0) = fromList finish0249Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0249 : finishSupport ⟨true, bits4 4⟩ support0933 = 1 • support0922 := by
  have hs : support0933 = fromList finish0249Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0249Chunk0]
  have hn : (finish0249Raw0 : Multiset ℕ) = 1 • (supportNumbers0922 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0922] using hm

private def finish0250Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366]
private def finish0250Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 36, 38, 45, 47, 101, 103, 108, 110]
private theorem finish0250Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0250Input0) = fromList finish0250Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0250 : finishSupport ⟨false, bits4 4⟩ support0935 = 1 • support0936 := by
  have hs : support0935 = fromList finish0250Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0250Chunk0]
  have hn : (finish0250Raw0 : Multiset ℕ) = 1 • (supportNumbers0936 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0936] using hm

private def finish0251Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 801, 803, 805, 807, 808, 810, 812, 814, 864, 866, 868, 870, 873, 875, 877, 879]
private def finish0251Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 32, 34, 36, 38, 41, 43, 45, 47, 97, 99, 101, 103, 104, 106, 108, 110, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 33, 35, 37, 39, 40, 42, 44, 46, 96, 98, 100, 102, 105, 107, 109, 111]
private theorem finish0251Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0251Input0) = fromList finish0251Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0251 : finishSupport ⟨true, bits4 4⟩ support0937 = 1 • support0938 := by
  have hs : support0937 = fromList finish0251Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0251Chunk0]
  have hn : (finish0251Raw0 : Multiset ℕ) = 1 • (supportNumbers0938 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0938] using hm

private def finish0252Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 289, 291, 293, 295, 352, 354, 356, 358, 425, 427, 429, 431, 488, 490, 492, 494]
private def finish0252Raw0 : List ℕ := [0, 2, 65, 67, 136, 138, 201, 203, 37, 39, 100, 102, 173, 175, 236, 238]
private theorem finish0252Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0252Input0) = fromList finish0252Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0252 : finishSupport ⟨false, bits4 4⟩ support0940 = 1 • support0941 := by
  have hs : support0940 = fromList finish0252Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0252Chunk0]
  have hn : (finish0252Raw0 : Multiset ℕ) = 1 • (supportNumbers0941 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0941] using hm

private def finish0253Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 289, 291, 293, 295, 352, 354, 356, 358, 425, 427, 429, 431, 488, 490, 492, 494, 513, 515, 517, 519, 576, 578, 580, 582, 649, 651, 653, 655, 712, 714, 716, 718, 800, 802, 804, 806, 865, 867, 869, 871, 936, 938, 940, 942, 1001, 1003, 1005, 1007]
private def finish0253Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 136, 138, 140, 142, 201, 203, 205, 207, 33, 35, 37, 39, 96, 98, 100, 102, 169, 171, 173, 175, 232, 234, 236, 238, 1, 3, 5, 7, 64, 66, 68, 70, 137, 139, 141, 143, 200, 202, 204, 206, 32, 34, 36, 38, 97, 99, 101, 103, 168, 170, 172, 174, 233, 235, 237, 239]
private theorem finish0253Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0253Input0) = fromList finish0253Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0253 : finishSupport ⟨true, bits4 4⟩ support0942 = 1 • support0604 := by
  have hs : support0942 = fromList finish0253Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0253Chunk0]
  have hn : (finish0253Raw0 : Multiset ℕ) = 1 • (supportNumbers0604 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0604] using hm

private def finish0254Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 130, 131, 134, 135, 136, 137, 140, 141, 194, 195, 198, 199, 200, 201, 204, 205]
private def finish0254Raw0 : List ℕ := [0, 1, 10, 11, 64, 65, 74, 75, 130, 131, 136, 137, 194, 195, 200, 201]
private theorem finish0254Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0254Input0) = fromList finish0254Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0254 : finishSupport ⟨false, bits4 4⟩ support0943 = 1 • support0944 := by
  have hs : support0943 = fromList finish0254Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0254Chunk0]
  have hn : (finish0254Raw0 : Multiset ℕ) = 1 • (supportNumbers0944 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0944] using hm

private def finish0255Input0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 130, 131, 134, 135, 136, 137, 140, 141, 194, 195, 198, 199, 200, 201, 204, 205, 514, 515, 518, 519, 520, 521, 524, 525, 578, 579, 582, 583, 584, 585, 588, 589, 640, 641, 644, 645, 650, 651, 654, 655, 704, 705, 708, 709, 714, 715, 718, 719]
private def finish0255Raw0 : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 64, 65, 68, 69, 74, 75, 78, 79, 130, 131, 134, 135, 136, 137, 140, 141, 194, 195, 198, 199, 200, 201, 204, 205, 2, 3, 6, 7, 8, 9, 12, 13, 66, 67, 70, 71, 72, 73, 76, 77, 128, 129, 132, 133, 138, 139, 142, 143, 192, 193, 196, 197, 202, 203, 206, 207]
private theorem finish0255Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0255Input0) = fromList finish0255Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0255 : finishSupport ⟨true, bits4 4⟩ support0945 = 1 • support0148 := by
  have hs : support0945 = fromList finish0255Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0255Chunk0]
  have hn : (finish0255Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0256Input0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196]
private def finish0256Raw0 : List ℕ := [0, 65, 129, 192]
private theorem finish0256Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0256Input0) = fromList finish0256Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0256 : finishSupport ⟨false, bits4 4⟩ support0947 = 1 • support0948 := by
  have hs : support0947 = fromList finish0256Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0256Chunk0]
  have hn : (finish0256Raw0 : Multiset ℕ) = 1 • (supportNumbers0948 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0948] using hm

private def finish0257Input0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 515, 519, 578, 582, 642, 646, 707, 711]
private def finish0257Raw0 : List ℕ := [0, 4, 65, 69, 129, 133, 192, 196, 3, 7, 66, 70, 130, 134, 195, 199]
private theorem finish0257Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0257Input0) = fromList finish0257Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0257 : finishSupport ⟨true, bits4 4⟩ support0949 = 1 • support0908 := by
  have hs : support0949 = fromList finish0257Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0257Chunk0]
  have hn : (finish0257Raw0 : Multiset ℕ) = 1 • (supportNumbers0908 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0908] using hm

private def finish0258Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 297, 299, 301, 303, 360, 362, 364, 366, 424, 426, 428, 430, 489, 491, 493, 495]
private def finish0258Raw0 : List ℕ := [0, 2, 65, 67, 129, 131, 192, 194, 45, 47, 108, 110, 172, 174, 237, 239]
private theorem finish0258Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0258Input0) = fromList finish0258Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0258 : finishSupport ⟨false, bits4 4⟩ support0951 = 1 • support0952 := by
  have hs : support0951 = fromList finish0258Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0258Chunk0]
  have hn : (finish0258Raw0 : Multiset ℕ) = 1 • (supportNumbers0952 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0952] using hm

private def finish0259Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 297, 299, 301, 303, 360, 362, 364, 366, 424, 426, 428, 430, 489, 491, 493, 495, 513, 515, 517, 519, 576, 578, 580, 582, 640, 642, 644, 646, 705, 707, 709, 711, 808, 810, 812, 814, 873, 875, 877, 879, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def finish0259Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 129, 131, 133, 135, 192, 194, 196, 198, 41, 43, 45, 47, 104, 106, 108, 110, 168, 170, 172, 174, 233, 235, 237, 239, 1, 3, 5, 7, 64, 66, 68, 70, 128, 130, 132, 134, 193, 195, 197, 199, 40, 42, 44, 46, 105, 107, 109, 111, 169, 171, 173, 175, 232, 234, 236, 238]
private theorem finish0259Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0259Input0) = fromList finish0259Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0259 : finishSupport ⟨true, bits4 4⟩ support0953 = 1 • support0954 := by
  have hs : support0953 = fromList finish0259Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0259Chunk0]
  have hn : (finish0259Raw0 : Multiset ℕ) = 1 • (supportNumbers0954 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0954] using hm

private def finish0260Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207]
private def finish0260Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 129, 131, 136, 138, 192, 194, 201, 203]
private theorem finish0260Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0260Input0) = fromList finish0260Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0260 : finishSupport ⟨false, bits4 4⟩ support0082 = 1 • support0955 := by
  have hs : support0082 = fromList finish0260Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0260Chunk0]
  have hn : (finish0260Raw0 : Multiset ℕ) = 1 • (supportNumbers0955 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0955] using hm

private def finish0261Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 513, 515, 517, 519, 520, 522, 524, 526, 576, 578, 580, 582, 585, 587, 589, 591, 640, 642, 644, 646, 649, 651, 653, 655, 705, 707, 709, 711, 712, 714, 716, 718]
private def finish0261Raw0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 1, 3, 5, 7, 8, 10, 12, 14, 64, 66, 68, 70, 73, 75, 77, 79, 128, 130, 132, 134, 137, 139, 141, 143, 193, 195, 197, 199, 200, 202, 204, 206]
private theorem finish0261Chunk0 : finishSupport ⟨true, bits4 4⟩ (fromList finish0261Input0) = fromList finish0261Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0261 : finishSupport ⟨true, bits4 4⟩ support0226 = 1 • support0148 := by
  have hs : support0226 = fromList finish0261Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0261Chunk0]
  have hn : (finish0261Raw0 : Multiset ℕ) = 1 • (supportNumbers0148 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0148] using hm

private def finish0262Input0 : List ℕ := [0, 2, 4, 6, 9, 11, 13, 15, 65, 67, 69, 71, 72, 74, 76, 78, 129, 131, 133, 135, 136, 138, 140, 142, 192, 194, 196, 198, 201, 203, 205, 207, 288, 290, 292, 294, 297, 299, 301, 303, 353, 355, 357, 359, 360, 362, 364, 366, 417, 419, 421, 423, 424, 426, 428, 430, 480, 482, 484, 486, 489, 491, 493, 495]
private def finish0262Raw0 : List ℕ := [0, 2, 9, 11, 65, 67, 72, 74, 129, 131, 136, 138, 192, 194, 201, 203, 36, 38, 45, 47, 101, 103, 108, 110, 165, 167, 172, 174, 228, 230, 237, 239]
private theorem finish0262Chunk0 : finishSupport ⟨false, bits4 4⟩ (fromList finish0262Input0) = fromList finish0262Raw0 := by
  rw [finishSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem finish0262 : finishSupport ⟨false, bits4 4⟩ support0957 = 1 • support0958 := by
  have hs : support0957 = fromList finish0262Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [finishSupport_add, finish0262Chunk0]
  have hn : (finish0262Raw0 : Multiset ℕ) = 1 • (supportNumbers0958 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0958] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
