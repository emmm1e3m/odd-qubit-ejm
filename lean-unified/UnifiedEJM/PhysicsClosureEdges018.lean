import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0357Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0357Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 408, 792, 409, 793, 410, 794, 411, 795, 412, 796, 413, 797, 414, 798, 415, 799, 472, 856, 473, 857, 474, 858, 475, 859, 476, 860, 477, 861, 478, 862, 479, 863]
private theorem transition0357Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0357Input0) = fromList transition0357Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0357 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0045 = 1 • support0087 := by
  have hs : support0045 = fromList transition0357Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0357Chunk0]
  have hn : (transition0357Raw0 : Multiset ℕ) = 1 • (supportNumbers0087 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0087] using hm

private def transition0358Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0358Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private theorem transition0358Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0358Input0) = fromList transition0358Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0358 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0045 = 1 • support0086 := by
  have hs : support0045 = fromList transition0358Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0358Chunk0]
  have hn : (transition0358Raw0 : Multiset ℕ) = 1 • (supportNumbers0086 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0086] using hm

private def transition0359Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0359Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 154, 155, 158, 159, 218, 219, 222, 223]
private theorem transition0359Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0359Input0) = fromList transition0359Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0359 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0086 = 1 • support0758 := by
  have hs : support0086 = fromList transition0359Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0359Chunk0]
  have hn : (transition0359Raw0 : Multiset ℕ) = 1 • (supportNumbers0758 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0758] using hm

private def transition0360Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479]
private def transition0360Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 728, 729, 154, 155, 732, 733, 158, 159, 664, 665, 218, 219, 668, 669, 222, 223]
private theorem transition0360Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0360Input0) = fromList transition0360Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0360 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0086 = 1 • support0760 := by
  have hs : support0086 = fromList transition0360Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0360Chunk0]
  have hn : (transition0360Raw0 : Multiset ℕ) = 1 • (supportNumbers0760 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0760] using hm

private def transition0361Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 664, 665, 666, 667, 668, 669, 670, 671, 728, 729, 730, 731, 732, 733, 734, 735]
private def transition0361Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 408, 952, 409, 953, 410, 954, 411, 955, 412, 956, 413, 957, 414, 958, 415, 959, 472, 1016, 473, 1017, 474, 1018, 475, 1019, 476, 1020, 477, 1021, 478, 1022, 479, 1023]
private theorem transition0361Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0361Input0) = fromList transition0361Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0361 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0045 = 1 • support0761 := by
  have hs : support0045 = fromList transition0361Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0361Chunk0]
  have hn : (transition0361Raw0 : Multiset ℕ) = 1 • (supportNumbers0761 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0761] using hm

private def transition0362Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0362Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 152, 153, 154, 155, 156, 157, 158, 159, 216, 217, 218, 219, 220, 221, 222, 223, 288, 289, 290, 291, 292, 293, 294, 295, 352, 353, 354, 355, 356, 357, 358, 359, 440, 441, 442, 443, 444, 445, 446, 447, 504, 505, 506, 507, 508, 509, 510, 511]
private theorem transition0362Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0362Input0) = fromList transition0362Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0362 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0761 = 1 • support0762 := by
  have hs : support0761 = fromList transition0362Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0362Chunk0]
  have hn : (transition0362Raw0 : Multiset ℕ) = 1 • (supportNumbers0762 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0762] using hm

private def transition0363Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 408, 409, 410, 411, 412, 413, 414, 415, 472, 473, 474, 475, 476, 477, 478, 479, 544, 545, 546, 547, 548, 549, 550, 551, 608, 609, 610, 611, 612, 613, 614, 615, 952, 953, 954, 955, 956, 957, 958, 959, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]
private def transition0363Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 152, 728, 153, 729, 154, 730, 155, 731, 156, 732, 157, 733, 158, 734, 159, 735, 216, 664, 217, 665, 218, 666, 219, 667, 220, 668, 221, 669, 222, 670, 223, 671, 288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 440, 1016, 441, 1017, 442, 1018, 443, 1019, 444, 1020, 445, 1021, 446, 1022, 447, 1023, 504, 952, 505, 953, 506, 954, 507, 955, 508, 956, 509, 957, 510, 958, 511, 959]
private theorem transition0363Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0363Input0) = fromList transition0363Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0363 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0761 = 1 • support0764 := by
  have hs : support0761 = fromList transition0363Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0363Chunk0]
  have hn : (transition0363Raw0 : Multiset ℕ) = 1 • (supportNumbers0764 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0764] using hm

private def transition0364Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0364Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition0364Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0364Input0) = fromList transition0364Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0364 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0046 = 1 • support0088 := by
  have hs : support0046 = fromList transition0364Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0364Chunk0]
  have hn : (transition0364Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition0365Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0365Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 728, 729, 730, 731, 732, 733, 734, 735, 136, 137, 138, 139, 140, 141, 142, 143, 528, 529, 530, 531, 532, 533, 534, 535, 200, 201, 202, 203, 204, 205, 206, 207, 592, 593, 594, 595, 596, 597, 598, 599]
private theorem transition0365Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0365Input0) = fromList transition0365Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0365 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0046 = 1 • support0089 := by
  have hs : support0046 = fromList transition0365Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0365Chunk0]
  have hn : (transition0365Raw0 : Multiset ℕ) = 1 • (supportNumbers0089 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0089] using hm

private def transition0366Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0366Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private theorem transition0366Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0366Input0) = fromList transition0366Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0366 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0046 = 1 • support0088 := by
  have hs : support0046 = fromList transition0366Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0366Chunk0]
  have hn : (transition0366Raw0 : Multiset ℕ) = 1 • (supportNumbers0088 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0088] using hm

private def transition0367Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0367Raw0 : List ℕ := [0, 1, 4, 5, 64, 65, 68, 69, 136, 137, 140, 141, 200, 201, 204, 205]
private theorem transition0367Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0367Input0) = fromList transition0367Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0367 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0088 = 1 • support0766 := by
  have hs : support0088 = fromList transition0367Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0367Chunk0]
  have hn : (transition0367Raw0 : Multiset ℕ) = 1 • (supportNumbers0766 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0766] using hm

private def transition0368Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207]
private def transition0368Raw0 : List ℕ := [0, 1, 578, 579, 4, 5, 582, 583, 64, 65, 514, 515, 68, 69, 518, 519, 136, 137, 714, 715, 140, 141, 718, 719, 200, 201, 650, 651, 204, 205, 654, 655]
private theorem transition0368Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0368Input0) = fromList transition0368Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0368 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0088 = 1 • support0768 := by
  have hs : support0088 = fromList transition0368Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0368Chunk0]
  have hn : (transition0368Raw0 : Multiset ℕ) = 1 • (supportNumbers0768 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0768] using hm

private def transition0369Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0369Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 632, 633, 634, 635, 636, 637, 638, 639, 136, 137, 138, 139, 140, 141, 142, 143, 688, 689, 690, 691, 692, 693, 694, 695, 200, 201, 202, 203, 204, 205, 206, 207, 752, 753, 754, 755, 756, 757, 758, 759]
private theorem transition0369Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0369Input0) = fromList transition0369Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0369 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0046 = 1 • support0769 := by
  have hs : support0046 = fromList transition0369Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0369Chunk0]
  have hn : (transition0369Raw0 : Multiset ℕ) = 1 • (supportNumbers0769 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0769] using hm

private def transition0370Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition0370Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 312, 313, 314, 315, 316, 317, 318, 319, 376, 377, 378, 379, 380, 381, 382, 383, 432, 433, 434, 435, 436, 437, 438, 439, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition0370Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0370Input0) = fromList transition0370Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0370 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0769 = 1 • support0770 := by
  have hs : support0769 = fromList transition0370Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0370Chunk0]
  have hn : (transition0370Raw0 : Multiset ℕ) = 1 • (supportNumbers0770 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0770] using hm

private def transition0371Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 64, 65, 66, 67, 68, 69, 70, 71, 136, 137, 138, 139, 140, 141, 142, 143, 200, 201, 202, 203, 204, 205, 206, 207, 568, 569, 570, 571, 572, 573, 574, 575, 632, 633, 634, 635, 636, 637, 638, 639, 688, 689, 690, 691, 692, 693, 694, 695, 752, 753, 754, 755, 756, 757, 758, 759]
private def transition0371Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 136, 712, 137, 713, 138, 714, 139, 715, 140, 716, 141, 717, 142, 718, 143, 719, 200, 648, 201, 649, 202, 650, 203, 651, 204, 652, 205, 653, 206, 654, 207, 655, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition0371Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0371Input0) = fromList transition0371Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0371 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0769 = 1 • support0771 := by
  have hs : support0769 = fromList transition0371Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0371Chunk0]
  have hn : (transition0371Raw0 : Multiset ℕ) = 1 • (supportNumbers0771 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0771] using hm

private def transition0372Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition0372Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 88, 89, 90, 91, 92, 93, 94, 95, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition0372Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0372Input0) = fromList transition0372Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition0372Input1 : List ℕ := [640, 641, 642, 643, 644, 645, 646, 647, 664, 665, 666, 667, 668, 669, 670, 671, 704, 705, 706, 707, 708, 709, 710, 711, 728, 729, 730, 731, 732, 733, 734, 735, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855]
private def transition0372Raw1 : List ℕ := [384, 385, 386, 387, 388, 389, 390, 391, 408, 409, 410, 411, 412, 413, 414, 415, 448, 449, 450, 451, 452, 453, 454, 455, 472, 473, 474, 475, 476, 477, 478, 479, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343]
private theorem transition0372Chunk1 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0372Input1) = fromList transition0372Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0372 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0047 = 1 • support0090 := by
  have hs : support0047 = fromList transition0372Input0 + fromList transition0372Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0372Chunk0, transition0372Chunk1]
  have hn : (transition0372Raw0 : Multiset ℕ) + (transition0372Raw1 : Multiset ℕ) = 1 • (supportNumbers0090 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0090] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
