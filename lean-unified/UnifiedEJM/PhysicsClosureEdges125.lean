import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2258Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2258Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition2258Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2258Input0) = fromList transition2258Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2258 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0320 = 1 • support0229 := by
  have hs : support0320 = fromList transition2258Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2258Chunk0]
  have hn : (transition2258Raw0 : Multiset ℕ) = 1 • (supportNumbers0229 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0229] using hm

private def transition2259Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2259Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 672, 673, 674, 675, 676, 677, 678, 679, 736, 737, 738, 739, 740, 741, 742, 743]
private theorem transition2259Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2259Input0) = fromList transition2259Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2259 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0320 = 1 • support1595 := by
  have hs : support0320 = fromList transition2259Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2259Chunk0]
  have hn : (transition2259Raw0 : Multiset ℕ) = 1 • (supportNumbers1595 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1595] using hm

private def transition2260Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2260Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition2260Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2260Input0) = fromList transition2260Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2260Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 896, 897, 898, 899, 900, 901, 902, 903, 960, 961, 962, 963, 964, 965, 966, 967]
private def transition2260Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition2260Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2260Input1) = fromList transition2260Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2260 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0321 = 2 • support0320 := by
  have hs : support0321 = fromList transition2260Input0 + fromList transition2260Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2260Chunk0, transition2260Chunk1]
  have hn : (transition2260Raw0 : Multiset ℕ) + (transition2260Raw1 : Multiset ℕ) = 2 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition2261Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2261Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583, 0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 128, 512, 129, 513, 130, 514, 131, 515, 132, 516, 133, 517, 134, 518, 135, 519, 192, 576, 193, 577, 194, 578, 195, 579, 196, 580, 197, 581, 198, 582, 199, 583]
private theorem transition2261Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2261Input0) = fromList transition2261Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2261Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 896, 897, 898, 899, 900, 901, 902, 903, 960, 961, 962, 963, 964, 965, 966, 967]
private def transition2261Raw1 : List ℕ := [256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839, 256, 896, 257, 897, 258, 898, 259, 899, 260, 900, 261, 901, 262, 902, 263, 903, 320, 960, 321, 961, 322, 962, 323, 963, 324, 964, 325, 965, 326, 966, 327, 967, 384, 768, 385, 769, 386, 770, 387, 771, 388, 772, 389, 773, 390, 774, 391, 775, 448, 832, 449, 833, 450, 834, 451, 835, 452, 836, 453, 837, 454, 838, 455, 839]
private theorem transition2261Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2261Input1) = fromList transition2261Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2261 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0321 = 2 • support0321 := by
  have hs : support0321 = fromList transition2261Input0 + fromList transition2261Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2261Chunk0, transition2261Chunk1]
  have hn : (transition2261Raw0 : Multiset ℕ) + (transition2261Raw1 : Multiset ℕ) = 2 • (supportNumbers0321 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0321] using hm

private def transition2262Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2262Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199]
private theorem transition2262Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2262Input0) = fromList transition2262Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2262Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 896, 897, 898, 899, 900, 901, 902, 903, 960, 961, 962, 963, 964, 965, 966, 967]
private def transition2262Raw1 : List ℕ := [256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private theorem transition2262Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2262Input1) = fromList transition2262Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2262 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0321 = 2 • support0320 := by
  have hs : support0321 = fromList transition2262Input0 + fromList transition2262Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2262Chunk0, transition2262Chunk1]
  have hn : (transition2262Raw0 : Multiset ℕ) + (transition2262Raw1 : Multiset ℕ) = 2 • (supportNumbers0320 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0320] using hm

private def transition2263Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 128, 129, 130, 131, 132, 133, 134, 135, 192, 193, 194, 195, 196, 197, 198, 199, 256, 257, 258, 259, 260, 261, 262, 263, 320, 321, 322, 323, 324, 325, 326, 327, 384, 385, 386, 387, 388, 389, 390, 391, 448, 449, 450, 451, 452, 453, 454, 455]
private def transition2263Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743, 0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 128, 672, 129, 673, 130, 674, 131, 675, 132, 676, 133, 677, 134, 678, 135, 679, 192, 736, 193, 737, 194, 738, 195, 739, 196, 740, 197, 741, 198, 742, 199, 743]
private theorem transition2263Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2263Input0) = fromList transition2263Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition2263Input1 : List ℕ := [512, 513, 514, 515, 516, 517, 518, 519, 576, 577, 578, 579, 580, 581, 582, 583, 640, 641, 642, 643, 644, 645, 646, 647, 704, 705, 706, 707, 708, 709, 710, 711, 768, 769, 770, 771, 772, 773, 774, 775, 832, 833, 834, 835, 836, 837, 838, 839, 896, 897, 898, 899, 900, 901, 902, 903, 960, 961, 962, 963, 964, 965, 966, 967]
private def transition2263Raw1 : List ℕ := [256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 256, 800, 257, 801, 258, 802, 259, 803, 260, 804, 261, 805, 262, 806, 263, 807, 320, 864, 321, 865, 322, 866, 323, 867, 324, 868, 325, 869, 326, 870, 327, 871, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999]
private theorem transition2263Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2263Input1) = fromList transition2263Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2263 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0321 = 2 • support1427 := by
  have hs : support0321 = fromList transition2263Input0 + fromList transition2263Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2263Chunk0, transition2263Chunk1]
  have hn : (transition2263Raw0 : Multiset ℕ) + (transition2263Raw1 : Multiset ℕ) = 2 • (supportNumbers1427 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1427] using hm

private def transition2264Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition2264Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2264Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2264Input0) = fromList transition2264Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2264 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0322 = 1 • support0020 := by
  have hs : support0322 = fromList transition2264Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2264Chunk0]
  have hn : (transition2264Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition2265Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition2265Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2265Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2265Input0) = fromList transition2265Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2265 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0322 = 1 • support0020 := by
  have hs : support0322 = fromList transition2265Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2265Chunk0]
  have hn : (transition2265Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition2266Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition2266Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2266Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2266Input0) = fromList transition2266Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2266 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0322 = 1 • support0020 := by
  have hs : support0322 = fromList transition2266Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2266Chunk0]
  have hn : (transition2266Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition2267Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 280, 281, 282, 283, 284, 285, 286, 287, 344, 345, 346, 347, 348, 349, 350, 351]
private def transition2267Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 24, 25, 26, 27, 28, 29, 30, 31, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2267Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2267Input0) = fromList transition2267Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2267 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0322 = 1 • support0020 := by
  have hs : support0322 = fromList transition2267Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2267Chunk0]
  have hn : (transition2267Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition2268Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2268Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition2268Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2268Input0) = fromList transition2268Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2268 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0020 = 1 • support0020 := by
  have hs : support0020 = fromList transition2268Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2268Chunk0]
  have hn : (transition2268Raw0 : Multiset ℕ) = 1 • (supportNumbers0020 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0020] using hm

private def transition2269Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition2269Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 24, 600, 25, 601, 26, 602, 27, 603, 28, 604, 29, 605, 30, 606, 31, 607, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 88, 536, 89, 537, 90, 538, 91, 539, 92, 540, 93, 541, 94, 542, 95, 543]
private theorem transition2269Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2269Input0) = fromList transition2269Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2269 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0020 = 1 • support0235 := by
  have hs : support0020 = fromList transition2269Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2269Chunk0]
  have hn : (transition2269Raw0 : Multiset ℕ) = 1 • (supportNumbers0235 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0235] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
