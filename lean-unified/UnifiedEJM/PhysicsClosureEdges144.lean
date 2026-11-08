import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2475Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition2475Raw0 : List ℕ := [0, 2, 129, 131, 545, 547, 672, 674]
private theorem transition2475Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2475Input0) = fromList transition2475Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2475 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0358 = 1 • support1657 := by
  have hs : support0358 = fromList transition2475Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2475Chunk0]
  have hn : (transition2475Raw0 : Multiset ℕ) = 1 • (supportNumbers1657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1657] using hm

private def transition2476Input0 : List ℕ := [0, 2, 129, 131, 545, 547, 672, 674]
private def transition2476Raw0 : List ℕ := [0, 2, 129, 131, 289, 291, 416, 418]
private theorem transition2476Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2476Input0) = fromList transition2476Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2476 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1657 = 1 • support1658 := by
  have hs : support1657 = fromList transition2476Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2476Chunk0]
  have hn : (transition2476Raw0 : Multiset ℕ) = 1 • (supportNumbers1658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1658] using hm

private def transition2477Input0 : List ℕ := [0, 2, 129, 131, 545, 547, 672, 674]
private def transition2477Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 289, 865, 291, 867, 416, 992, 418, 994]
private theorem transition2477Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2477Input0) = fromList transition2477Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2477 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1657 = 1 • support1659 := by
  have hs : support1657 = fromList transition2477Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2477Chunk0]
  have hn : (transition2477Raw0 : Multiset ℕ) = 1 • (supportNumbers1659 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1659] using hm

private def transition2478Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 513, 515, 640, 642, 768, 770, 897, 899]
private def transition2478Raw0 : List ℕ := [0, 2, 129, 131, 1, 3, 128, 130, 257, 259, 384, 386, 256, 258, 385, 387]
private theorem transition2478Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2478Input0) = fromList transition2478Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2478 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0359 = 1 • support0273 := by
  have hs : support0359 = fromList transition2478Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2478Chunk0]
  have hn : (transition2478Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition2479Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 513, 515, 640, 642, 768, 770, 897, 899]
private def transition2479Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 1, 641, 3, 643, 128, 512, 130, 514, 257, 897, 259, 899, 384, 768, 386, 770, 256, 896, 258, 898, 385, 769, 387, 771]
private theorem transition2479Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2479Input0) = fromList transition2479Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2479 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0359 = 1 • support0274 := by
  have hs : support0359 = fromList transition2479Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2479Chunk0]
  have hn : (transition2479Raw0 : Multiset ℕ) = 1 • (supportNumbers0274 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0274] using hm

private def transition2480Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 513, 515, 640, 642, 768, 770, 897, 899]
private def transition2480Raw0 : List ℕ := [0, 2, 129, 131, 1, 3, 128, 130, 257, 259, 384, 386, 256, 258, 385, 387]
private theorem transition2480Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2480Input0) = fromList transition2480Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2480 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0359 = 1 • support0273 := by
  have hs : support0359 = fromList transition2480Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2480Chunk0]
  have hn : (transition2480Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition2481Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 513, 515, 640, 642, 768, 770, 897, 899]
private def transition2481Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 1, 545, 3, 547, 128, 672, 130, 674, 257, 801, 259, 803, 384, 928, 386, 930, 256, 800, 258, 802, 385, 929, 387, 931]
private theorem transition2481Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2481Input0) = fromList transition2481Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2481 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0359 = 1 • support1323 := by
  have hs : support0359 = fromList transition2481Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2481Chunk0]
  have hn : (transition2481Raw0 : Multiset ℕ) = 1 • (supportNumbers1323 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1323] using hm

private def transition2482Input0 : List ℕ := [0, 2, 129, 131, 521, 523, 648, 650]
private def transition2482Raw0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private theorem transition2482Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2482Input0) = fromList transition2482Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2482 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0360 = 1 • support0422 := by
  have hs : support0360 = fromList transition2482Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2482Chunk0]
  have hn : (transition2482Raw0 : Multiset ℕ) = 1 • (supportNumbers0422 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0422] using hm

private def transition2483Input0 : List ℕ := [0, 2, 129, 131, 521, 523, 648, 650]
private def transition2483Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 265, 905, 267, 907, 392, 776, 394, 778]
private theorem transition2483Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2483Input0) = fromList transition2483Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2483 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0360 = 1 • support0423 := by
  have hs : support0360 = fromList transition2483Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2483Chunk0]
  have hn : (transition2483Raw0 : Multiset ℕ) = 1 • (supportNumbers0423 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0423] using hm

private def transition2484Input0 : List ℕ := [0, 2, 129, 131, 521, 523, 648, 650]
private def transition2484Raw0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private theorem transition2484Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2484Input0) = fromList transition2484Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2484 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0360 = 1 • support0422 := by
  have hs : support0360 = fromList transition2484Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2484Chunk0]
  have hn : (transition2484Raw0 : Multiset ℕ) = 1 • (supportNumbers0422 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0422] using hm

private def transition2485Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2485Raw0 : List ℕ := [0, 129, 11, 138]
private theorem transition2485Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2485Input0) = fromList transition2485Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2485 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0422 = 1 • support1661 := by
  have hs : support0422 = fromList transition2485Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2485Chunk0]
  have hn : (transition2485Raw0 : Multiset ℕ) = 1 • (supportNumbers1661 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1661] using hm

private def transition2486Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394]
private def transition2486Raw0 : List ℕ := [0, 578, 129, 707, 585, 11, 712, 138]
private theorem transition2486Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2486Input0) = fromList transition2486Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2486 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0422 = 1 • support1662 := by
  have hs : support0422 = fromList transition2486Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2486Chunk0]
  have hn : (transition2486Raw0 : Multiset ℕ) = 1 • (supportNumbers1662 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1662] using hm

private def transition2487Input0 : List ℕ := [0, 2, 129, 131, 521, 523, 648, 650]
private def transition2487Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 265, 809, 267, 811, 392, 936, 394, 938]
private theorem transition2487Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2487Input0) = fromList transition2487Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2487 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0360 = 1 • support1664 := by
  have hs : support0360 = fromList transition2487Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2487Chunk0]
  have hn : (transition2487Raw0 : Multiset ℕ) = 1 • (supportNumbers1664 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1664] using hm

private def transition2488Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 544, 546, 673, 675, 809, 811, 936, 938]
private def transition2488Raw0 : List ℕ := [0, 2, 129, 131, 9, 11, 136, 138, 288, 290, 417, 419, 297, 299, 424, 426]
private theorem transition2488Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2488Input0) = fromList transition2488Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2488 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1664 = 1 • support0841 := by
  have hs : support1664 = fromList transition2488Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2488Chunk0]
  have hn : (transition2488Raw0 : Multiset ℕ) = 1 • (supportNumbers0841 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0841] using hm

private def transition2489Input0 : List ℕ := [0, 2, 129, 131, 265, 267, 392, 394, 544, 546, 673, 675, 809, 811, 936, 938]
private def transition2489Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 9, 585, 11, 587, 136, 712, 138, 714, 288, 864, 290, 866, 417, 993, 419, 995, 297, 873, 299, 875, 424, 1000, 426, 1002]
private theorem transition2489Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2489Input0) = fromList transition2489Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2489 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1664 = 1 • support0842 := by
  have hs : support1664 = fromList transition2489Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2489Chunk0]
  have hn : (transition2489Raw0 : Multiset ℕ) = 1 • (supportNumbers0842 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0842] using hm

private def transition2490Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 513, 515, 521, 523, 640, 642, 648, 650]
private def transition2490Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private theorem transition2490Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2490Input0) = fromList transition2490Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2490 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0361 = 1 • support0028 := by
  have hs : support0361 = fromList transition2490Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2490Chunk0]
  have hn : (transition2490Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition2491Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 513, 515, 521, 523, 640, 642, 648, 650]
private def transition2491Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 257, 897, 259, 899, 265, 905, 267, 907, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition2491Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2491Input0) = fromList transition2491Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2491 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0361 = 1 • support0029 := by
  have hs : support0361 = fromList transition2491Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2491Chunk0]
  have hn : (transition2491Raw0 : Multiset ℕ) = 1 • (supportNumbers0029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0029] using hm

private def transition2492Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 513, 515, 521, 523, 640, 642, 648, 650]
private def transition2492Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394]
private theorem transition2492Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2492Input0) = fromList transition2492Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2492 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0361 = 1 • support0028 := by
  have hs : support0361 = fromList transition2492Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2492Chunk0]
  have hn : (transition2492Raw0 : Multiset ℕ) = 1 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition2493Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 513, 515, 521, 523, 640, 642, 648, 650]
private def transition2493Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 257, 801, 259, 803, 265, 809, 267, 811, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition2493Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2493Input0) = fromList transition2493Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2493 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0361 = 1 • support0563 := by
  have hs : support0361 = fromList transition2493Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2493Chunk0]
  have hn : (transition2493Raw0 : Multiset ℕ) = 1 • (supportNumbers0563 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0563] using hm

private def transition2494Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition2494Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition2494Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2494Input0) = fromList transition2494Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2494 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0362 = 1 • support0268 := by
  have hs : support0362 = fromList transition2494Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2494Chunk0]
  have hn : (transition2494Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition2495Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition2495Raw0 : List ℕ := [0, 2, 648, 650, 129, 131, 521, 523, 640, 642, 8, 10, 513, 515, 137, 139]
private theorem transition2495Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2495Input0) = fromList transition2495Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2495 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0362 = 1 • support0361 := by
  have hs : support0362 = fromList transition2495Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2495Chunk0]
  have hn : (transition2495Raw0 : Multiset ℕ) = 1 • (supportNumbers0361 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0361] using hm

private def transition2496Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition2496Raw0 : List ℕ := [0, 2, 129, 131, 8, 10, 137, 139]
private theorem transition2496Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2496Input0) = fromList transition2496Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2496 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0362 = 1 • support0268 := by
  have hs : support0362 = fromList transition2496Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2496Chunk0]
  have hn : (transition2496Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition2497Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition2497Raw0 : List ℕ := [0, 2, 552, 554, 129, 131, 681, 683, 544, 546, 8, 10, 673, 675, 137, 139]
private theorem transition2497Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2497Input0) = fromList transition2497Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2497 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0362 = 1 • support1514 := by
  have hs : support0362 = fromList transition2497Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2497Chunk0]
  have hn : (transition2497Raw0 : Multiset ℕ) = 1 • (supportNumbers1514 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1514] using hm

private def transition2498Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 513, 515, 521, 523, 640, 642, 648, 650, 769, 771, 777, 779, 896, 898, 904, 906]
private def transition2498Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 257, 259, 265, 267, 384, 386, 392, 394]
private theorem transition2498Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2498Input0) = fromList transition2498Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2498 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0363 = 2 • support0028 := by
  have hs : support0363 = fromList transition2498Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2498Chunk0]
  have hn : (transition2498Raw0 : Multiset ℕ) = 2 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition2499Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 513, 515, 521, 523, 640, 642, 648, 650, 769, 771, 777, 779, 896, 898, 904, 906]
private def transition2499Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 257, 897, 259, 899, 265, 905, 267, 907, 384, 768, 386, 770, 392, 776, 394, 778, 257, 897, 259, 899, 265, 905, 267, 907, 384, 768, 386, 770, 392, 776, 394, 778]
private theorem transition2499Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2499Input0) = fromList transition2499Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2499 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0363 = 2 • support0029 := by
  have hs : support0363 = fromList transition2499Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2499Chunk0]
  have hn : (transition2499Raw0 : Multiset ℕ) = 2 • (supportNumbers0029 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0029] using hm

private def transition2500Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 513, 515, 521, 523, 640, 642, 648, 650, 769, 771, 777, 779, 896, 898, 904, 906]
private def transition2500Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 0, 2, 8, 10, 129, 131, 137, 139, 257, 259, 265, 267, 384, 386, 392, 394, 257, 259, 265, 267, 384, 386, 392, 394]
private theorem transition2500Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2500Input0) = fromList transition2500Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2500 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0363 = 2 • support0028 := by
  have hs : support0363 = fromList transition2500Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2500Chunk0]
  have hn : (transition2500Raw0 : Multiset ℕ) = 2 • (supportNumbers0028 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0028] using hm

private def transition2501Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 513, 515, 521, 523, 640, 642, 648, 650, 769, 771, 777, 779, 896, 898, 904, 906]
private def transition2501Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 257, 801, 259, 803, 265, 809, 267, 811, 384, 928, 386, 930, 392, 936, 394, 938, 257, 801, 259, 803, 265, 809, 267, 811, 384, 928, 386, 930, 392, 936, 394, 938]
private theorem transition2501Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2501Input0) = fromList transition2501Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2501 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0363 = 2 • support0563 := by
  have hs : support0363 = fromList transition2501Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2501Chunk0]
  have hn : (transition2501Raw0 : Multiset ℕ) = 2 • (supportNumbers0563 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0563] using hm

private def transition2502Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 512, 513, 514, 515, 640, 641, 642, 643]
private def transition2502Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private theorem transition2502Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2502Input0) = fromList transition2502Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2502 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0364 = 1 • support0273 := by
  have hs : support0364 = fromList transition2502Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2502Chunk0]
  have hn : (transition2502Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition2503Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 512, 513, 514, 515, 640, 641, 642, 643]
private def transition2503Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 256, 896, 257, 897, 258, 898, 259, 899, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition2503Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2503Input0) = fromList transition2503Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2503 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0364 = 1 • support0274 := by
  have hs : support0364 = fromList transition2503Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2503Chunk0]
  have hn : (transition2503Raw0 : Multiset ℕ) = 1 • (supportNumbers0274 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0274] using hm

private def transition2504Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 512, 513, 514, 515, 640, 641, 642, 643]
private def transition2504Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private theorem transition2504Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2504Input0) = fromList transition2504Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2504 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0364 = 1 • support0273 := by
  have hs : support0364 = fromList transition2504Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2504Chunk0]
  have hn : (transition2504Raw0 : Multiset ℕ) = 1 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition2505Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 512, 513, 514, 515, 640, 641, 642, 643]
private def transition2505Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 256, 800, 257, 801, 258, 802, 259, 803, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition2505Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2505Input0) = fromList transition2505Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2505 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0364 = 1 • support1323 := by
  have hs : support0364 = fromList transition2505Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2505Chunk0]
  have hn : (transition2505Raw0 : Multiset ℕ) = 1 • (supportNumbers1323 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1323] using hm

private def transition2506Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition2506Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private theorem transition2506Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2506Input0) = fromList transition2506Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2506 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0114 = 1 • support0114 := by
  have hs : support0114 = fromList transition2506Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2506Chunk0]
  have hn : (transition2506Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition2507Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition2507Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523]
private theorem transition2507Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2507Input0) = fromList transition2507Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2507 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0114 = 1 • support0115 := by
  have hs : support0114 = fromList transition2507Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2507Chunk0]
  have hn : (transition2507Raw0 : Multiset ℕ) = 1 • (supportNumbers0115 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0115] using hm

private def transition2508Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition2508Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private theorem transition2508Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2508Input0) = fromList transition2508Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2508 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0114 = 1 • support0114 := by
  have hs : support0114 = fromList transition2508Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2508Chunk0]
  have hn : (transition2508Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition2509Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition2509Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683]
private theorem transition2509Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2509Input0) = fromList transition2509Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2509 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0114 = 1 • support0846 := by
  have hs : support0114 = fromList transition2509Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2509Chunk0]
  have hn : (transition2509Raw0 : Multiset ℕ) = 1 • (supportNumbers0846 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0846] using hm

private def transition2510Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition2510Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition2510Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2510Input0) = fromList transition2510Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2510 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0365 = 1 • support0030 := by
  have hs : support0365 = fromList transition2510Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2510Chunk0]
  have hn : (transition2510Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition2511Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition2511Raw0 : List ℕ := [0, 1, 2, 3, 640, 641, 642, 643]
private theorem transition2511Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2511Input0) = fromList transition2511Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2511 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0365 = 1 • support0116 := by
  have hs : support0365 = fromList transition2511Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2511Chunk0]
  have hn : (transition2511Raw0 : Multiset ℕ) = 1 • (supportNumbers0116 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0116] using hm

private def transition2512Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition2512Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition2512Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2512Input0) = fromList transition2512Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2512 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0365 = 1 • support0030 := by
  have hs : support0365 = fromList transition2512Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2512Chunk0]
  have hn : (transition2512Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition2513Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition2513Raw0 : List ℕ := [0, 1, 2, 3, 544, 545, 546, 547]
private theorem transition2513Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2513Input0) = fromList transition2513Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2513 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0365 = 1 • support0847 := by
  have hs : support0365 = fromList transition2513Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2513Chunk0]
  have hn : (transition2513Raw0 : Multiset ℕ) = 1 • (supportNumbers0847 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0847] using hm

private def transition2514Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 640, 641, 642, 643, 896, 897, 898, 899]
private def transition2514Raw0 : List ℕ := [0, 1, 2, 3, 0, 1, 2, 3, 384, 385, 386, 387, 384, 385, 386, 387]
private theorem transition2514Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2514Input0) = fromList transition2514Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2514 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0366 = 2 • support0189 := by
  have hs : support0366 = fromList transition2514Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2514Chunk0]
  have hn : (transition2514Raw0 : Multiset ℕ) = 2 • (supportNumbers0189 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0189] using hm

private def transition2515Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 640, 641, 642, 643, 896, 897, 898, 899]
private def transition2515Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 0, 640, 1, 641, 2, 642, 3, 643, 384, 768, 385, 769, 386, 770, 387, 771, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition2515Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2515Input0) = fromList transition2515Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2515 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0366 = 2 • support0190 := by
  have hs : support0366 = fromList transition2515Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2515Chunk0]
  have hn : (transition2515Raw0 : Multiset ℕ) = 2 • (supportNumbers0190 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0190] using hm

private def transition2516Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 640, 641, 642, 643, 896, 897, 898, 899]
private def transition2516Raw0 : List ℕ := [0, 1, 2, 3, 0, 1, 2, 3, 384, 385, 386, 387, 384, 385, 386, 387]
private theorem transition2516Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2516Input0) = fromList transition2516Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2516 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0366 = 2 • support0189 := by
  have hs : support0366 = fromList transition2516Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2516Chunk0]
  have hn : (transition2516Raw0 : Multiset ℕ) = 2 • (supportNumbers0189 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0189] using hm

private def transition2517Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 640, 641, 642, 643, 896, 897, 898, 899]
private def transition2517Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 0, 544, 1, 545, 2, 546, 3, 547, 384, 928, 385, 929, 386, 930, 387, 931, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition2517Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2517Input0) = fromList transition2517Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2517 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0366 = 2 • support1080 := by
  have hs : support0366 = fromList transition2517Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2517Chunk0]
  have hn : (transition2517Raw0 : Multiset ℕ) = 2 • (supportNumbers1080 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1080] using hm

private def transition2518Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition2518Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition2518Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2518Input0) = fromList transition2518Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2518 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0012 = 1 • support0012 := by
  have hs : support0012 = fromList transition2518Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2518Chunk0]
  have hn : (transition2518Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition2519Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition2519Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671]
private theorem transition2519Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2519Input0) = fromList transition2519Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2519 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0012 = 1 • support0369 := by
  have hs : support0012 = fromList transition2519Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2519Chunk0]
  have hn : (transition2519Raw0 : Multiset ℕ) = 1 • (supportNumbers0369 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0369] using hm

private def transition2520Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition2520Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition2520Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2520Input0) = fromList transition2520Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2520 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0012 = 1 • support0012 := by
  have hs : support0012 = fromList transition2520Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2520Chunk0]
  have hn : (transition2520Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition2521Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition2521Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575]
private theorem transition2521Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2521Input0) = fromList transition2521Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2521 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0012 = 1 • support1522 := by
  have hs : support0012 = fromList transition2521Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2521Chunk0]
  have hn : (transition2521Raw0 : Multiset ℕ) = 1 • (supportNumbers1522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1522] using hm

private def transition2522Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition2522Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition2522Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2522Input0) = fromList transition2522Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2522 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0367 = 1 • support0117 := by
  have hs : support0367 = fromList transition2522Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2522Chunk0]
  have hn : (transition2522Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition2523Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition2523Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 512, 513, 514, 515, 156, 157, 158, 159]
private theorem transition2523Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2523Input0) = fromList transition2523Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2523 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0367 = 1 • support0424 := by
  have hs : support0367 = fromList transition2523Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2523Chunk0]
  have hn : (transition2523Raw0 : Multiset ℕ) = 1 • (supportNumbers0424 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0424] using hm

private def transition2524Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition2524Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159]
private theorem transition2524Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2524Input0) = fromList transition2524Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2524 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0367 = 1 • support0117 := by
  have hs : support0367 = fromList transition2524Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2524Chunk0]
  have hn : (transition2524Raw0 : Multiset ℕ) = 1 • (supportNumbers0117 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0117] using hm

private def transition2525Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition2525Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 672, 673, 674, 675, 156, 157, 158, 159]
private theorem transition2525Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2525Input0) = fromList transition2525Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2525 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0367 = 1 • support1665 := by
  have hs : support0367 = fromList transition2525Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2525Chunk0]
  have hn : (transition2525Raw0 : Multiset ℕ) = 1 • (supportNumbers1665 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1665] using hm

private def transition2526Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 572, 573, 574, 575, 672, 673, 674, 675]
private def transition2526Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 316, 317, 318, 319, 416, 417, 418, 419]
private theorem transition2526Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2526Input0) = fromList transition2526Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2526 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1665 = 1 • support1666 := by
  have hs : support1665 = fromList transition2526Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2526Chunk0]
  have hn : (transition2526Raw0 : Multiset ℕ) = 1 • (supportNumbers1666 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1666] using hm

private def transition2527Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 572, 573, 574, 575, 672, 673, 674, 675]
private def transition2527Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 156, 732, 157, 733, 158, 734, 159, 735, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition2527Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2527Input0) = fromList transition2527Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2527 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1665 = 1 • support1667 := by
  have hs : support1665 = fromList transition2527Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2527Chunk0]
  have hn : (transition2527Raw0 : Multiset ℕ) = 1 • (supportNumbers1667 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1667] using hm

private def transition2528Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799]
private def transition2528Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 384, 385, 386, 387, 412, 413, 414, 415, 256, 257, 258, 259, 284, 285, 286, 287]
private theorem transition2528Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2528Input0) = fromList transition2528Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2528 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0368 = 1 • support0194 := by
  have hs : support0368 = fromList transition2528Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2528Chunk0]
  have hn : (transition2528Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2529Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 640, 641, 642, 643, 668, 669, 670, 671, 768, 769, 770, 771, 796, 797, 798, 799]
private def transition2529Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 156, 540, 157, 541, 158, 542, 159, 543, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927]
private theorem transition2529Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2529Input0) = fromList transition2529Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2529 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0368 = 1 • support0195 := by
  have hs : support0368 = fromList transition2529Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2529Chunk0]
  have hn : (transition2529Raw0 : Multiset ℕ) = 1 • (supportNumbers0195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0195] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
