import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition0439Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0439Raw0 : List ℕ := [0, 8, 128, 136, 2, 10, 130, 138]
private theorem transition0439Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0439Input0) = fromList transition0439Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0439 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0103 = 1 • support0173 := by
  have hs : support0103 = fromList transition0439Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0439Chunk0]
  have hn : (transition0439Raw0 : Multiset ℕ) = 1 • (supportNumbers0173 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0173] using hm

private def transition0440Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394]
private def transition0440Raw0 : List ℕ := [0, 578, 8, 586, 128, 706, 136, 714, 576, 2, 584, 10, 704, 130, 712, 138]
private theorem transition0440Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0440Input0) = fromList transition0440Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0440 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0103 = 1 • support0814 := by
  have hs : support0103 = fromList transition0440Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0440Chunk0]
  have hn : (transition0440Raw0 : Multiset ℕ) = 1 • (supportNumbers0814 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0814] using hm

private def transition0441Input0 : List ℕ := [0, 2, 136, 138, 264, 266, 384, 386, 520, 522, 640, 642, 768, 770, 904, 906]
private def transition0441Raw0 : List ℕ := [0, 544, 2, 546, 136, 680, 138, 682, 8, 552, 10, 554, 128, 672, 130, 674, 264, 808, 266, 810, 384, 928, 386, 930, 256, 800, 258, 802, 392, 936, 394, 938]
private theorem transition0441Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0441Input0) = fromList transition0441Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0441 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0055 = 1 • support0816 := by
  have hs : support0055 = fromList transition0441Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0441Chunk0]
  have hn : (transition0441Raw0 : Multiset ℕ) = 1 • (supportNumbers0816 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0816] using hm

private def transition0442Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 544, 546, 552, 554, 672, 674, 680, 682, 800, 802, 808, 810, 928, 930, 936, 938]
private def transition0442Raw0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 0, 2, 8, 10, 128, 130, 136, 138, 288, 290, 296, 298, 416, 418, 424, 426, 288, 290, 296, 298, 416, 418, 424, 426]
private theorem transition0442Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0442Input0) = fromList transition0442Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0442 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0816 = 2 • support0657 := by
  have hs : support0816 = fromList transition0442Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0442Chunk0]
  have hn : (transition0442Raw0 : Multiset ℕ) = 2 • (supportNumbers0657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0657] using hm

private def transition0443Input0 : List ℕ := [0, 2, 8, 10, 128, 130, 136, 138, 256, 258, 264, 266, 384, 386, 392, 394, 544, 546, 552, 554, 672, 674, 680, 682, 800, 802, 808, 810, 928, 930, 936, 938]
private def transition0443Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 128, 704, 130, 706, 136, 712, 138, 714, 0, 576, 2, 578, 8, 584, 10, 586, 128, 704, 130, 706, 136, 712, 138, 714, 288, 864, 290, 866, 296, 872, 298, 874, 416, 992, 418, 994, 424, 1000, 426, 1002, 288, 864, 290, 866, 296, 872, 298, 874, 416, 992, 418, 994, 424, 1000, 426, 1002]
private theorem transition0443Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0443Input0) = fromList transition0443Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0443 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0816 = 2 • support0658 := by
  have hs : support0816 = fromList transition0443Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0443Chunk0]
  have hn : (transition0443Raw0 : Multiset ℕ) = 2 • (supportNumbers0658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0658] using hm

private def transition0444Input0 : List ℕ := [0, 2, 521, 523]
private def transition0444Raw0 : List ℕ := [0, 2, 265, 267]
private theorem transition0444Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0444Input0) = fromList transition0444Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0444 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0056 = 1 • support0105 := by
  have hs : support0056 = fromList transition0444Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0444Chunk0]
  have hn : (transition0444Raw0 : Multiset ℕ) = 1 • (supportNumbers0105 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0105] using hm

private def transition0445Input0 : List ℕ := [0, 2, 521, 523]
private def transition0445Raw0 : List ℕ := [0, 640, 2, 642, 265, 905, 267, 907]
private theorem transition0445Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0445Input0) = fromList transition0445Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0445 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0056 = 1 • support0106 := by
  have hs : support0056 = fromList transition0445Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0445Chunk0]
  have hn : (transition0445Raw0 : Multiset ℕ) = 1 • (supportNumbers0106 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0106] using hm

private def transition0446Input0 : List ℕ := [0, 2, 521, 523]
private def transition0446Raw0 : List ℕ := [0, 2, 265, 267]
private theorem transition0446Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0446Input0) = fromList transition0446Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0446 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0056 = 1 • support0105 := by
  have hs : support0056 = fromList transition0446Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0446Chunk0]
  have hn : (transition0446Raw0 : Multiset ℕ) = 1 • (supportNumbers0105 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0105] using hm

private def transition0447Input0 : List ℕ := [0, 2, 265, 267]
private def transition0447Raw0 : List ℕ := [0, 11]
private theorem transition0447Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0447Input0) = fromList transition0447Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0447 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0105 = 1 • support0817 := by
  have hs : support0105 = fromList transition0447Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0447Chunk0]
  have hn : (transition0447Raw0 : Multiset ℕ) = 1 • (supportNumbers0817 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0817] using hm

private def transition0448Input0 : List ℕ := [0, 2, 265, 267]
private def transition0448Raw0 : List ℕ := [0, 578, 585, 11]
private theorem transition0448Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0448Input0) = fromList transition0448Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0448 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0105 = 1 • support0818 := by
  have hs : support0105 = fromList transition0448Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0448Chunk0]
  have hn : (transition0448Raw0 : Multiset ℕ) = 1 • (supportNumbers0818 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0818] using hm

private def transition0449Input0 : List ℕ := [0, 2, 521, 523]
private def transition0449Raw0 : List ℕ := [0, 544, 2, 546, 265, 809, 267, 811]
private theorem transition0449Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0449Input0) = fromList transition0449Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0449 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0056 = 1 • support0820 := by
  have hs : support0056 = fromList transition0449Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0449Chunk0]
  have hn : (transition0449Raw0 : Multiset ℕ) = 1 • (supportNumbers0820 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0820] using hm

private def transition0450Input0 : List ℕ := [0, 2, 265, 267, 544, 546, 809, 811]
private def transition0450Raw0 : List ℕ := [0, 2, 9, 11, 288, 290, 297, 299]
private theorem transition0450Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0450Input0) = fromList transition0450Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0450 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0820 = 1 • support0821 := by
  have hs : support0820 = fromList transition0450Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0450Chunk0]
  have hn : (transition0450Raw0 : Multiset ℕ) = 1 • (supportNumbers0821 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0821] using hm

private def transition0451Input0 : List ℕ := [0, 2, 265, 267, 544, 546, 809, 811]
private def transition0451Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 288, 864, 290, 866, 297, 873, 299, 875]
private theorem transition0451Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0451Input0) = fromList transition0451Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0451 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0820 = 1 • support0822 := by
  have hs : support0820 = fromList transition0451Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0451Chunk0]
  have hn : (transition0451Raw0 : Multiset ℕ) = 1 • (supportNumbers0822 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0822] using hm

private def transition0452Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0452Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0452Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0452Input0) = fromList transition0452Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0452 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0057 = 1 • support0053 := by
  have hs : support0057 = fromList transition0452Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0452Chunk0]
  have hn : (transition0452Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0453Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0453Raw0 : List ℕ := [0, 2, 521, 523, 641, 643, 136, 138]
private theorem transition0453Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0453Input0) = fromList transition0453Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0453 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0057 = 1 • support0107 := by
  have hs : support0057 = fromList transition0453Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0453Chunk0]
  have hn : (transition0453Raw0 : Multiset ℕ) = 1 • (supportNumbers0107 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0107] using hm

private def transition0454Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0454Raw0 : List ℕ := [0, 2, 136, 138]
private theorem transition0454Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0454Input0) = fromList transition0454Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0454 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0057 = 1 • support0053 := by
  have hs : support0057 = fromList transition0454Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0454Chunk0]
  have hn : (transition0454Raw0 : Multiset ℕ) = 1 • (supportNumbers0053 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0053] using hm

private def transition0455Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394]
private def transition0455Raw0 : List ℕ := [0, 2, 681, 683, 545, 547, 136, 138]
private theorem transition0455Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0455Input0) = fromList transition0455Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0455 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0057 = 1 • support0824 := by
  have hs : support0057 = fromList transition0455Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0455Chunk0]
  have hn : (transition0455Raw0 : Multiset ℕ) = 1 • (supportNumbers0824 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0824] using hm

private def transition0456Input0 : List ℕ := [0, 2, 136, 138, 545, 547, 681, 683]
private def transition0456Raw0 : List ℕ := [0, 2, 136, 138, 289, 291, 425, 427]
private theorem transition0456Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0456Input0) = fromList transition0456Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0456 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0824 = 1 • support0825 := by
  have hs : support0824 = fromList transition0456Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0456Chunk0]
  have hn : (transition0456Raw0 : Multiset ℕ) = 1 • (supportNumbers0825 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0825] using hm

private def transition0457Input0 : List ℕ := [0, 2, 136, 138, 545, 547, 681, 683]
private def transition0457Raw0 : List ℕ := [0, 576, 2, 578, 136, 712, 138, 714, 289, 865, 291, 867, 425, 1001, 427, 1003]
private theorem transition0457Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0457Input0) = fromList transition0457Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0457 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0824 = 1 • support0826 := by
  have hs : support0824 = fromList transition0457Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0457Chunk0]
  have hn : (transition0457Raw0 : Multiset ℕ) = 1 • (supportNumbers0826 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0826] using hm

private def transition0458Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 521, 523, 640, 642, 776, 778, 897, 899]
private def transition0458Raw0 : List ℕ := [0, 2, 137, 139, 1, 3, 136, 138, 265, 267, 384, 386, 264, 266, 385, 387]
private theorem transition0458Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0458Input0) = fromList transition0458Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0458 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0058 = 1 • support0108 := by
  have hs : support0058 = fromList transition0458Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0458Chunk0]
  have hn : (transition0458Raw0 : Multiset ℕ) = 1 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition0459Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 521, 523, 640, 642, 776, 778, 897, 899]
private def transition0459Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 1, 641, 3, 643, 136, 520, 138, 522, 265, 905, 267, 907, 384, 768, 386, 770, 264, 904, 266, 906, 385, 769, 387, 771]
private theorem transition0459Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0459Input0) = fromList transition0459Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0459 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0058 = 1 • support0109 := by
  have hs : support0058 = fromList transition0459Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0459Chunk0]
  have hn : (transition0459Raw0 : Multiset ℕ) = 1 • (supportNumbers0109 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0109] using hm

private def transition0460Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 521, 523, 640, 642, 776, 778, 897, 899]
private def transition0460Raw0 : List ℕ := [0, 2, 137, 139, 1, 3, 136, 138, 265, 267, 384, 386, 264, 266, 385, 387]
private theorem transition0460Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0460Input0) = fromList transition0460Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0460 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0058 = 1 • support0108 := by
  have hs : support0058 = fromList transition0460Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0460Chunk0]
  have hn : (transition0460Raw0 : Multiset ℕ) = 1 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition0461Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0461Raw0 : List ℕ := [0, 1, 136, 137, 10, 11, 130, 131]
private theorem transition0461Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0461Input0) = fromList transition0461Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0461 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0108 = 1 • support0698 := by
  have hs : support0108 = fromList transition0461Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0461Chunk0]
  have hn : (transition0461Raw0 : Multiset ℕ) = 1 • (supportNumbers0698 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0698] using hm

private def transition0462Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387]
private def transition0462Raw0 : List ℕ := [0, 1, 578, 579, 136, 137, 714, 715, 584, 585, 10, 11, 704, 705, 130, 131]
private theorem transition0462Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0462Input0) = fromList transition0462Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0462 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0108 = 1 • support0828 := by
  have hs : support0108 = fromList transition0462Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0462Chunk0]
  have hn : (transition0462Raw0 : Multiset ℕ) = 1 • (supportNumbers0828 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0828] using hm

private def transition0463Input0 : List ℕ := [0, 2, 137, 139, 257, 259, 392, 394, 521, 523, 640, 642, 776, 778, 897, 899]
private def transition0463Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 1, 545, 3, 547, 136, 680, 138, 682, 265, 809, 267, 811, 384, 928, 386, 930, 264, 808, 266, 810, 385, 929, 387, 931]
private theorem transition0463Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0463Input0) = fromList transition0463Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0463 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0058 = 1 • support0830 := by
  have hs : support0058 = fromList transition0463Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0463Chunk0]
  have hn : (transition0463Raw0 : Multiset ℕ) = 1 • (supportNumbers0830 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0830] using hm

private def transition0464Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 544, 545, 546, 547, 680, 681, 682, 683, 808, 809, 810, 811, 928, 929, 930, 931]
private def transition0464Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 8, 9, 10, 11, 128, 129, 130, 131, 288, 289, 290, 291, 424, 425, 426, 427, 296, 297, 298, 299, 416, 417, 418, 419]
private theorem transition0464Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0464Input0) = fromList transition0464Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0464 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0830 = 1 • support0564 := by
  have hs : support0830 = fromList transition0464Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0464Chunk0]
  have hn : (transition0464Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition0465Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 264, 265, 266, 267, 384, 385, 386, 387, 544, 545, 546, 547, 680, 681, 682, 683, 808, 809, 810, 811, 928, 929, 930, 931]
private def transition0465Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition0465Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0465Input0) = fromList transition0465Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0465 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0830 = 1 • support0565 := by
  have hs : support0830 = fromList transition0465Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0465Chunk0]
  have hn : (transition0465Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition0466Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0466Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0466Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0466Input0) = fromList transition0466Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0466 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0059 = 1 • support0110 := by
  have hs : support0059 = fromList transition0466Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0466Chunk0]
  have hn : (transition0466Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0467Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0467Raw0 : List ℕ := [0, 2, 649, 651, 129, 131, 520, 522]
private theorem transition0467Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0467Input0) = fromList transition0467Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0467 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0059 = 1 • support0111 := by
  have hs : support0059 = fromList transition0467Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0467Chunk0]
  have hn : (transition0467Raw0 : Multiset ℕ) = 1 • (supportNumbers0111 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0111] using hm

private def transition0468Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0468Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition0468Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0468Input0) = fromList transition0468Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0468 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0059 = 1 • support0110 := by
  have hs : support0059 = fromList transition0468Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0468Chunk0]
  have hn : (transition0468Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition0469Input0 : List ℕ := [0, 2, 129, 131]
private def transition0469Raw0 : List ℕ := [0, 129]
private theorem transition0469Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0469Input0) = fromList transition0469Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0469 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0110 = 1 • support0831 := by
  have hs : support0110 = fromList transition0469Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0469Chunk0]
  have hn : (transition0469Raw0 : Multiset ℕ) = 1 • (supportNumbers0831 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0831] using hm

private def transition0470Input0 : List ℕ := [0, 2, 129, 131]
private def transition0470Raw0 : List ℕ := [0, 578, 129, 707]
private theorem transition0470Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0470Input0) = fromList transition0470Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0470 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0110 = 1 • support0832 := by
  have hs : support0110 = fromList transition0470Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0470Chunk0]
  have hn : (transition0470Raw0 : Multiset ℕ) = 1 • (supportNumbers0832 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0832] using hm

private def transition0471Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138]
private def transition0471Raw0 : List ℕ := [0, 2, 553, 555, 129, 131, 680, 682]
private theorem transition0471Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0471Input0) = fromList transition0471Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0471 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0059 = 1 • support0834 := by
  have hs : support0059 = fromList transition0471Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0471Chunk0]
  have hn : (transition0471Raw0 : Multiset ℕ) = 1 • (supportNumbers0834 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0834] using hm

private def transition0472Input0 : List ℕ := [0, 2, 129, 131, 553, 555, 680, 682]
private def transition0472Raw0 : List ℕ := [0, 2, 129, 131, 297, 299, 424, 426]
private theorem transition0472Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0472Input0) = fromList transition0472Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0472 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0834 = 1 • support0835 := by
  have hs : support0834 = fromList transition0472Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0472Chunk0]
  have hn : (transition0472Raw0 : Multiset ℕ) = 1 • (supportNumbers0835 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0835] using hm

private def transition0473Input0 : List ℕ := [0, 2, 129, 131, 553, 555, 680, 682]
private def transition0473Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 297, 873, 299, 875, 424, 1000, 426, 1002]
private theorem transition0473Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0473Input0) = fromList transition0473Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0473 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0834 = 1 • support0836 := by
  have hs : support0834 = fromList transition0473Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0473Chunk0]
  have hn : (transition0473Raw0 : Multiset ℕ) = 1 • (supportNumbers0836 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0836] using hm

private def transition0474Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 512, 514, 521, 523, 641, 643, 648, 650]
private def transition0474Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private theorem transition0474Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0474Input0) = fromList transition0474Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0474 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0060 = 1 • support0112 := by
  have hs : support0060 = fromList transition0474Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0474Chunk0]
  have hn : (transition0474Raw0 : Multiset ℕ) = 1 • (supportNumbers0112 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0112] using hm

private def transition0475Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 512, 514, 521, 523, 641, 643, 648, 650]
private def transition0475Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 129, 513, 131, 515, 136, 520, 138, 522, 256, 896, 258, 898, 265, 905, 267, 907, 385, 769, 387, 771, 392, 776, 394, 778]
private theorem transition0475Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0475Input0) = fromList transition0475Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0475 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0060 = 1 • support0113 := by
  have hs : support0060 = fromList transition0475Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0475Chunk0]
  have hn : (transition0475Raw0 : Multiset ℕ) = 1 • (supportNumbers0113 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0113] using hm

private def transition0476Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 512, 514, 521, 523, 641, 643, 648, 650]
private def transition0476Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private theorem transition0476Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0476Input0) = fromList transition0476Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0476 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0060 = 1 • support0112 := by
  have hs : support0060 = fromList transition0476Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0476Chunk0]
  have hn : (transition0476Raw0 : Multiset ℕ) = 1 • (supportNumbers0112 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0112] using hm

private def transition0477Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0477Raw0 : List ℕ := [0, 9, 129, 136, 2, 11, 131, 138]
private theorem transition0477Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0477Input0) = fromList transition0477Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0477 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0112 = 1 • support0059 := by
  have hs : support0112 = fromList transition0477Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0477Chunk0]
  have hn : (transition0477Raw0 : Multiset ℕ) = 1 • (supportNumbers0059 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0059] using hm

private def transition0478Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394]
private def transition0478Raw0 : List ℕ := [0, 578, 9, 587, 129, 707, 136, 714, 576, 2, 585, 11, 705, 131, 712, 138]
private theorem transition0478Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0478Input0) = fromList transition0478Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0478 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0112 = 1 • support0838 := by
  have hs : support0112 = fromList transition0478Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0478Chunk0]
  have hn : (transition0478Raw0 : Multiset ℕ) = 1 • (supportNumbers0838 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0838] using hm

private def transition0479Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 512, 514, 521, 523, 641, 643, 648, 650]
private def transition0479Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 129, 673, 131, 675, 136, 680, 138, 682, 256, 800, 258, 802, 265, 809, 267, 811, 385, 929, 387, 931, 392, 936, 394, 938]
private theorem transition0479Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0479Input0) = fromList transition0479Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0479 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0060 = 1 • support0840 := by
  have hs : support0060 = fromList transition0479Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0479Chunk0]
  have hn : (transition0479Raw0 : Multiset ℕ) = 1 • (supportNumbers0840 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0840] using hm

private def transition0480Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 544, 546, 553, 555, 673, 675, 680, 682, 800, 802, 809, 811, 929, 931, 936, 938]
private def transition0480Raw0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 0, 2, 9, 11, 129, 131, 136, 138, 288, 290, 297, 299, 417, 419, 424, 426, 288, 290, 297, 299, 417, 419, 424, 426]
private theorem transition0480Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0480Input0) = fromList transition0480Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0480 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0840 = 2 • support0841 := by
  have hs : support0840 = fromList transition0480Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0480Chunk0]
  have hn : (transition0480Raw0 : Multiset ℕ) = 2 • (supportNumbers0841 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0841] using hm

private def transition0481Input0 : List ℕ := [0, 2, 9, 11, 129, 131, 136, 138, 256, 258, 265, 267, 385, 387, 392, 394, 544, 546, 553, 555, 673, 675, 680, 682, 800, 802, 809, 811, 929, 931, 936, 938]
private def transition0481Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714, 0, 576, 2, 578, 9, 585, 11, 587, 129, 705, 131, 707, 136, 712, 138, 714, 288, 864, 290, 866, 297, 873, 299, 875, 417, 993, 419, 995, 424, 1000, 426, 1002, 288, 864, 290, 866, 297, 873, 299, 875, 417, 993, 419, 995, 424, 1000, 426, 1002]
private theorem transition0481Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0481Input0) = fromList transition0481Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0481 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0840 = 2 • support0842 := by
  have hs : support0840 = fromList transition0481Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0481Chunk0]
  have hn : (transition0481Raw0 : Multiset ℕ) = 2 • (supportNumbers0842 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0842] using hm

private def transition0482Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0482Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition0482Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0482Input0) = fromList transition0482Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0482 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0061 = 1 • support0114 := by
  have hs : support0061 = fromList transition0482Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0482Chunk0]
  have hn : (transition0482Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition0483Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0483Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 128, 129, 130, 131, 520, 521, 522, 523, 640, 641, 642, 643, 8, 9, 10, 11, 512, 513, 514, 515, 136, 137, 138, 139]
private theorem transition0483Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition0483Input0) = fromList transition0483Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0483 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0061 = 1 • support0115 := by
  have hs : support0061 = fromList transition0483Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0483Chunk0]
  have hn : (transition0483Raw0 : Multiset ℕ) = 1 • (supportNumbers0115 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0115] using hm

private def transition0484Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0484Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition0484Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition0484Input0) = fromList transition0484Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0484 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0061 = 1 • support0114 := by
  have hs : support0061 = fromList transition0484Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0484Chunk0]
  have hn : (transition0484Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition0485Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0485Raw0 : List ℕ := [0, 1, 8, 9, 128, 129, 136, 137]
private theorem transition0485Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0485Input0) = fromList transition0485Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0485 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0114 = 1 • support0717 := by
  have hs : support0114 = fromList transition0485Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0485Chunk0]
  have hn : (transition0485Raw0 : Multiset ℕ) = 1 • (supportNumbers0717 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0717] using hm

private def transition0486Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition0486Raw0 : List ℕ := [0, 1, 578, 579, 8, 9, 586, 587, 128, 129, 706, 707, 136, 137, 714, 715]
private theorem transition0486Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0486Input0) = fromList transition0486Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0486 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0114 = 1 • support0844 := by
  have hs : support0114 = fromList transition0486Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0486Chunk0]
  have hn : (transition0486Raw0 : Multiset ℕ) = 1 • (supportNumbers0844 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0844] using hm

private def transition0487Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition0487Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 128, 129, 130, 131, 680, 681, 682, 683, 544, 545, 546, 547, 8, 9, 10, 11, 672, 673, 674, 675, 136, 137, 138, 139]
private theorem transition0487Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition0487Input0) = fromList transition0487Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0487 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0061 = 1 • support0846 := by
  have hs : support0061 = fromList transition0487Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0487Chunk0]
  have hn : (transition0487Raw0 : Multiset ℕ) = 1 • (supportNumbers0846 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0846] using hm

private def transition0488Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 544, 545, 546, 547, 552, 553, 554, 555, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0488Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 288, 289, 290, 291, 296, 297, 298, 299, 416, 417, 418, 419, 424, 425, 426, 427]
private theorem transition0488Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition0488Input0) = fromList transition0488Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0488 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0846 = 1 • support0564 := by
  have hs : support0846 = fromList transition0488Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0488Chunk0]
  have hn : (transition0488Raw0 : Multiset ℕ) = 1 • (supportNumbers0564 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0564] using hm

private def transition0489Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 544, 545, 546, 547, 552, 553, 554, 555, 672, 673, 674, 675, 680, 681, 682, 683]
private def transition0489Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition0489Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition0489Input0) = fromList transition0489Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0489 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0846 = 1 • support0565 := by
  have hs : support0846 = fromList transition0489Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0489Chunk0]
  have hn : (transition0489Raw0 : Multiset ℕ) = 1 • (supportNumbers0565 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0565] using hm

private def transition0490Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 512, 513, 514, 515, 520, 521, 522, 523, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition0490Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition0490Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition0490Input0) = fromList transition0490Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition0490 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0062 = 2 • support0061 := by
  have hs : support0062 = fromList transition0490Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition0490Chunk0]
  have hn : (transition0490Raw0 : Multiset ℕ) = 2 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
