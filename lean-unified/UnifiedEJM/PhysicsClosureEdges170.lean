import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2958Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2958Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 9, 11, 13, 15, 72, 74, 76, 78, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 256, 258, 260, 262, 321, 323, 325, 327, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2958Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2958Input0) = fromList transition2958Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2958 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0440 = 1 • support0308 := by
  have hs : support0440 = fromList transition2958Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2958Chunk0]
  have hn : (transition2958Raw0 : Multiset ℕ) = 1 • (supportNumbers0308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0308] using hm

private def transition2959Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711, 768, 770, 772, 774, 833, 835, 837, 839, 905, 907, 909, 911, 968, 970, 972, 974]
private def transition2959Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 9, 553, 11, 555, 13, 557, 15, 559, 72, 616, 74, 618, 76, 620, 78, 622, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999, 256, 800, 258, 802, 260, 804, 262, 806, 321, 865, 323, 867, 325, 869, 327, 871, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2959Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2959Input0) = fromList transition2959Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2959 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0440 = 1 • support1397 := by
  have hs : support0440 = fromList transition2959Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2959Chunk0]
  have hn : (transition2959Raw0 : Multiset ℕ) = 1 • (supportNumbers1397 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1397] using hm

private def transition2960Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2960Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2960Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2960Input0) = fromList transition2960Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2960 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0441 = 1 • support0439 := by
  have hs : support0441 = fromList transition2960Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2960Chunk0]
  have hn : (transition2960Raw0 : Multiset ℕ) = 1 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2961Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2961Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 137, 521, 139, 523, 141, 525, 143, 527, 200, 584, 202, 586, 204, 588, 206, 590, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 384, 768, 386, 770, 388, 772, 390, 774, 449, 833, 451, 835, 453, 837, 455, 839]
private theorem transition2961Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2961Input0) = fromList transition2961Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2961 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0441 = 1 • support0440 := by
  have hs : support0441 = fromList transition2961Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2961Chunk0]
  have hn : (transition2961Raw0 : Multiset ℕ) = 1 • (supportNumbers0440 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0440] using hm

private def transition2962Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2962Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 265, 267, 269, 271, 328, 330, 332, 334, 384, 386, 388, 390, 449, 451, 453, 455]
private theorem transition2962Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2962Input0) = fromList transition2962Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2962 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0441 = 1 • support0439 := by
  have hs : support0441 = fromList transition2962Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2962Chunk0]
  have hn : (transition2962Raw0 : Multiset ℕ) = 1 • (supportNumbers0439 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0439] using hm

private def transition2963Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 137, 139, 141, 143, 200, 202, 204, 206, 521, 523, 525, 527, 584, 586, 588, 590, 640, 642, 644, 646, 705, 707, 709, 711]
private def transition2963Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 137, 681, 139, 683, 141, 685, 143, 687, 200, 744, 202, 746, 204, 748, 206, 750, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 384, 928, 386, 930, 388, 932, 390, 934, 449, 993, 451, 995, 453, 997, 455, 999]
private theorem transition2963Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2963Input0) = fromList transition2963Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2963 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0441 = 1 • support1693 := by
  have hs : support0441 = fromList transition2963Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2963Chunk0]
  have hn : (transition2963Raw0 : Multiset ℕ) = 1 • (supportNumbers1693 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1693] using hm

private def transition2964Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 521, 523, 525, 527, 584, 586, 588, 590, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2964Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2964Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2964Input0) = fromList transition2964Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2964 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0442 = 1 • support0464 := by
  have hs : support0442 = fromList transition2964Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2964Chunk0]
  have hn : (transition2964Raw0 : Multiset ℕ) = 1 • (supportNumbers0464 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0464] using hm

private def transition2965Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 521, 523, 525, 527, 584, 586, 588, 590, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2965Raw0 : List ℕ := [0, 640, 2, 642, 4, 644, 6, 646, 65, 705, 67, 707, 69, 709, 71, 711, 128, 512, 130, 514, 132, 516, 134, 518, 193, 577, 195, 579, 197, 581, 199, 583, 265, 905, 267, 907, 269, 909, 271, 911, 328, 968, 330, 970, 332, 972, 334, 974, 393, 777, 395, 779, 397, 781, 399, 783, 456, 840, 458, 842, 460, 844, 462, 846]
private theorem transition2965Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2965Input0) = fromList transition2965Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2965 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0442 = 1 • support0465 := by
  have hs : support0442 = fromList transition2965Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2965Chunk0]
  have hn : (transition2965Raw0 : Multiset ℕ) = 1 • (supportNumbers0465 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0465] using hm

private def transition2966Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 521, 523, 525, 527, 584, 586, 588, 590, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2966Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private theorem transition2966Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2966Input0) = fromList transition2966Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2966 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0442 = 1 • support0464 := by
  have hs : support0442 = fromList transition2966Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2966Chunk0]
  have hn : (transition2966Raw0 : Multiset ℕ) = 1 • (supportNumbers0464 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0464] using hm

private def transition2967Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2967Raw0 : List ℕ := [0, 4, 65, 69, 128, 132, 193, 197, 11, 15, 74, 78, 139, 143, 202, 206]
private theorem transition2967Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2967Input0) = fromList transition2967Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2967 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0464 = 1 • support1758 := by
  have hs : support0464 = fromList transition2967Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2967Chunk0]
  have hn : (transition2967Raw0 : Multiset ℕ) = 1 • (supportNumbers1758 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1758] using hm

private def transition2968Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462]
private def transition2968Raw0 : List ℕ := [0, 578, 4, 582, 65, 515, 69, 519, 128, 706, 132, 710, 193, 643, 197, 647, 585, 11, 589, 15, 520, 74, 524, 78, 713, 139, 717, 143, 648, 202, 652, 206]
private theorem transition2968Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2968Input0) = fromList transition2968Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2968 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0464 = 1 • support1760 := by
  have hs : support0464 = fromList transition2968Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2968Chunk0]
  have hn : (transition2968Raw0 : Multiset ℕ) = 1 • (supportNumbers1760 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1760] using hm

private def transition2969Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 521, 523, 525, 527, 584, 586, 588, 590, 649, 651, 653, 655, 712, 714, 716, 718]
private def transition2969Raw0 : List ℕ := [0, 544, 2, 546, 4, 548, 6, 550, 65, 609, 67, 611, 69, 613, 71, 615, 128, 672, 130, 674, 132, 676, 134, 678, 193, 737, 195, 739, 197, 741, 199, 743, 265, 809, 267, 811, 269, 813, 271, 815, 328, 872, 330, 874, 332, 876, 334, 878, 393, 937, 395, 939, 397, 941, 399, 943, 456, 1000, 458, 1002, 460, 1004, 462, 1006]
private theorem transition2969Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2969Input0) = fromList transition2969Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2969 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0442 = 1 • support1761 := by
  have hs : support0442 = fromList transition2969Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2969Chunk0]
  have hn : (transition2969Raw0 : Multiset ℕ) = 1 • (supportNumbers1761 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1761] using hm

private def transition2970Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 809, 811, 813, 815, 872, 874, 876, 878, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2970Raw0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 9, 11, 13, 15, 72, 74, 76, 78, 137, 139, 141, 143, 200, 202, 204, 206, 288, 290, 292, 294, 353, 355, 357, 359, 416, 418, 420, 422, 481, 483, 485, 487, 297, 299, 301, 303, 360, 362, 364, 366, 425, 427, 429, 431, 488, 490, 492, 494]
private theorem transition2970Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2970Input0) = fromList transition2970Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2970 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1761 = 1 • support1171 := by
  have hs : support1761 = fromList transition2970Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2970Chunk0]
  have hn : (transition2970Raw0 : Multiset ℕ) = 1 • (supportNumbers1171 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1171] using hm

private def transition2971Input0 : List ℕ := [0, 2, 4, 6, 65, 67, 69, 71, 128, 130, 132, 134, 193, 195, 197, 199, 265, 267, 269, 271, 328, 330, 332, 334, 393, 395, 397, 399, 456, 458, 460, 462, 544, 546, 548, 550, 609, 611, 613, 615, 672, 674, 676, 678, 737, 739, 741, 743, 809, 811, 813, 815, 872, 874, 876, 878, 937, 939, 941, 943, 1000, 1002, 1004, 1006]
private def transition2971Raw0 : List ℕ := [0, 576, 2, 578, 4, 580, 6, 582, 65, 513, 67, 515, 69, 517, 71, 519, 128, 704, 130, 706, 132, 708, 134, 710, 193, 641, 195, 643, 197, 645, 199, 647, 9, 585, 11, 587, 13, 589, 15, 591, 72, 520, 74, 522, 76, 524, 78, 526, 137, 713, 139, 715, 141, 717, 143, 719, 200, 648, 202, 650, 204, 652, 206, 654, 288, 864, 290, 866, 292, 868, 294, 870, 353, 801, 355, 803, 357, 805, 359, 807, 416, 992, 418, 994, 420, 996, 422, 998, 481, 929, 483, 931, 485, 933, 487, 935, 297, 873, 299, 875, 301, 877, 303, 879, 360, 808, 362, 810, 364, 812, 366, 814, 425, 1001, 427, 1003, 429, 1005, 431, 1007, 488, 936, 490, 938, 492, 940, 494, 942]
private theorem transition2971Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2971Input0) = fromList transition2971Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2971 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1761 = 1 • support1173 := by
  have hs : support1761 = fromList transition2971Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2971Chunk0]
  have hn : (transition2971Raw0 : Multiset ℕ) = 1 • (supportNumbers1173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1173] using hm

private def transition2972Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2972Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2972Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2972Input0) = fromList transition2972Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2972 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0088 = 1 • support0088 := by
  have hs : support0088 = fromList transition2972Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2972Chunk0]
  have hn : (transition2972Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2973Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2973Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 136, 520, 137, 521, 138, 522, 139, 523, 140, 524, 141, 525, 142, 526, 143, 527, 200, 584, 201, 585, 202, 586, 203, 587, 204, 588, 205, 589, 206, 590, 207, 591]
private theorem transition2973Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2973Input0) = fromList transition2973Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2973 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0088 = 1 • support0466 := by
  have hs : support0088 = fromList transition2973Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2973Chunk0]
  have hn : (transition2973Raw0 : Multiset ℕ) = 1 • (supportNumbers0466 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0466] using hm

private def transition2974Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2974Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition2974Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2974Input0) = fromList transition2974Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2974 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0088 = 1 • support0088 := by
  have hs : support0088 = fromList transition2974Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2974Chunk0]
  have hn : (transition2974Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition2975Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition2975Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 136, 680, 137, 681, 138, 682, 139, 683, 140, 684, 141, 685, 142, 686, 143, 687, 200, 744, 201, 745, 202, 746, 203, 747, 204, 748, 205, 749, 206, 750, 207, 751]
private theorem transition2975Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2975Input0) = fromList transition2975Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2975 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0088 = 1 • support1762 := by
  have hs : support0088 = fromList transition2975Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2975Chunk0]
  have hn : (transition2975Raw0 : Multiset ℕ) = 1 • (supportNumbers1762 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1762] using hm

private def transition2976Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 680, 681, 682, 683, 684, 685, 686, 687, 744, 745, 746, 747, 748, 749, 750, 751]
private def transition2976Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 424, 425, 426, 427, 428, 429, 430, 431, 488, 489, 490, 491, 492, 493, 494, 495]
private theorem transition2976Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2976Input0) = fromList transition2976Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2976 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1762 = 1 • support0747 := by
  have hs : support1762 = fromList transition2976Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2976Chunk0]
  have hn : (transition2976Raw0 : Multiset ℕ) = 1 • (supportNumbers0747 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0747] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
