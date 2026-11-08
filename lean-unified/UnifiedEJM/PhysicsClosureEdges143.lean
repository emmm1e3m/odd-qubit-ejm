import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2411Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 512, 514, 640, 642, 776, 778, 904, 906]
private def transition2411Raw0 : List ℕ := [0, 640, 2, 642, 128, 512, 130, 514, 8, 648, 10, 650, 136, 520, 138, 522, 256, 896, 258, 898, 384, 768, 386, 770, 264, 904, 266, 906, 392, 776, 394, 778]
private theorem transition2411Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2411Input0) = fromList transition2411Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2411 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0346 = 1 • support0104 := by
  have hs : support0346 = fromList transition2411Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2411Chunk0]
  have hn : (transition2411Raw0 : Multiset ℕ) = 1 • (supportNumbers0104 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0104] using hm

private def transition2412Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 512, 514, 640, 642, 776, 778, 904, 906]
private def transition2412Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138, 256, 258, 384, 386, 264, 266, 392, 394]
private theorem transition2412Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2412Input0) = fromList transition2412Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2412 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0346 = 1 • support0103 := by
  have hs : support0346 = fromList transition2412Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2412Chunk0]
  have hn : (transition2412Raw0 : Multiset ℕ) = 1 • (supportNumbers0103 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0103] using hm

private def transition2413Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 512, 514, 640, 642, 776, 778, 904, 906]
private def transition2413Raw0 : List ℕ := [0, 544, 2, 546, 128, 672, 130, 674, 8, 552, 10, 554, 136, 680, 138, 682, 256, 800, 258, 802, 384, 928, 386, 930, 264, 808, 266, 810, 392, 936, 394, 938]
private theorem transition2413Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2413Input0) = fromList transition2413Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2413 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0346 = 1 • support0816 := by
  have hs : support0346 = fromList transition2413Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2413Chunk0]
  have hn : (transition2413Raw0 : Multiset ℕ) = 1 • (supportNumbers0816 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0816] using hm

private def transition2414Input0 : List ℕ := [0, 2, 393, 395]
private def transition2414Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2414Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2414Input0) = fromList transition2414Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2414 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0347 = 1 • support0026 := by
  have hs : support0347 = fromList transition2414Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2414Chunk0]
  have hn : (transition2414Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2415Input0 : List ℕ := [0, 2, 393, 395]
private def transition2415Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2415Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2415Input0) = fromList transition2415Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2415 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0347 = 1 • support0026 := by
  have hs : support0347 = fromList transition2415Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2415Chunk0]
  have hn : (transition2415Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2416Input0 : List ℕ := [0, 2, 393, 395]
private def transition2416Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2416Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2416Input0) = fromList transition2416Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2416 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0347 = 1 • support0026 := by
  have hs : support0347 = fromList transition2416Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2416Chunk0]
  have hn : (transition2416Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2417Input0 : List ℕ := [0, 2, 393, 395]
private def transition2417Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2417Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2417Input0) = fromList transition2417Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2417 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0347 = 1 • support0026 := by
  have hs : support0347 = fromList transition2417Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2417Chunk0]
  have hn : (transition2417Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2418Input0 : List ℕ := [0, 2, 137, 139]
private def transition2418Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2418Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2418Input0) = fromList transition2418Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2418 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0026 = 1 • support0026 := by
  have hs : support0026 = fromList transition2418Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2418Chunk0]
  have hn : (transition2418Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2419Input0 : List ℕ := [0, 2, 137, 139]
private def transition2419Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715]
private theorem transition2419Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2419Input0) = fromList transition2419Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2419 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0026 = 1 • support1491 := by
  have hs : support0026 = fromList transition2419Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2419Chunk0]
  have hn : (transition2419Raw0 : Multiset ℕ) = 1 • (supportNumbers1491 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1491] using hm

private def transition2420Input0 : List ℕ := [0, 2, 393, 395, 640, 642, 777, 779]
private def transition2420Raw0 : List ℕ := [0, 2, 137, 139, 384, 386, 265, 267]
private theorem transition2420Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2420Input0) = fromList transition2420Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2420 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0348 = 1 • support0420 := by
  have hs : support0348 = fromList transition2420Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2420Chunk0]
  have hn : (transition2420Raw0 : Multiset ℕ) = 1 • (supportNumbers0420 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0420] using hm

private def transition2421Input0 : List ℕ := [0, 2, 393, 395, 640, 642, 777, 779]
private def transition2421Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 384, 768, 386, 770, 265, 905, 267, 907]
private theorem transition2421Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2421Input0) = fromList transition2421Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2421 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0348 = 1 • support0421 := by
  have hs : support0348 = fromList transition2421Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2421Chunk0]
  have hn : (transition2421Raw0 : Multiset ℕ) = 1 • (supportNumbers0421 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0421] using hm

private def transition2422Input0 : List ℕ := [0, 2, 393, 395, 640, 642, 777, 779]
private def transition2422Raw0 : List ℕ := [0, 2, 137, 139, 384, 386, 265, 267]
private theorem transition2422Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2422Input0) = fromList transition2422Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2422 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0348 = 1 • support0420 := by
  have hs : support0348 = fromList transition2422Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2422Chunk0]
  have hn : (transition2422Raw0 : Multiset ℕ) = 1 • (supportNumbers0420 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0420] using hm

private def transition2423Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2423Raw0 : List ℕ := [0, 137, 11, 130]
private theorem transition2423Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2423Input0) = fromList transition2423Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2423 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0420 = 1 • support1639 := by
  have hs : support0420 = fromList transition2423Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2423Chunk0]
  have hn : (transition2423Raw0 : Multiset ℕ) = 1 • (supportNumbers1639 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1639] using hm

private def transition2424Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386]
private def transition2424Raw0 : List ℕ := [0, 578, 137, 715, 585, 11, 704, 130]
private theorem transition2424Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2424Input0) = fromList transition2424Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2424 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0420 = 1 • support1640 := by
  have hs : support0420 = fromList transition2424Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2424Chunk0]
  have hn : (transition2424Raw0 : Multiset ℕ) = 1 • (supportNumbers1640 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1640] using hm

private def transition2425Input0 : List ℕ := [0, 2, 393, 395, 640, 642, 777, 779]
private def transition2425Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 384, 928, 386, 930, 265, 809, 267, 811]
private theorem transition2425Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2425Input0) = fromList transition2425Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2425 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0348 = 1 • support1642 := by
  have hs : support0348 = fromList transition2425Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2425Chunk0]
  have hn : (transition2425Raw0 : Multiset ℕ) = 1 • (supportNumbers1642 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1642] using hm

private def transition2426Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 544, 546, 681, 683, 809, 811, 928, 930]
private def transition2426Raw0 : List ℕ := [0, 2, 137, 139, 9, 11, 128, 130, 288, 290, 425, 427, 297, 299, 416, 418]
private theorem transition2426Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2426Input0) = fromList transition2426Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2426 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1642 = 1 • support1048 := by
  have hs : support1642 = fromList transition2426Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2426Chunk0]
  have hn : (transition2426Raw0 : Multiset ℕ) = 1 • (supportNumbers1048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1048] using hm

private def transition2427Input0 : List ℕ := [0, 2, 137, 139, 265, 267, 384, 386, 544, 546, 681, 683, 809, 811, 928, 930]
private def transition2427Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 9, 585, 11, 587, 128, 704, 130, 706, 288, 864, 290, 866, 425, 1001, 427, 1003, 297, 873, 299, 875, 416, 992, 418, 994]
private theorem transition2427Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2427Input0) = fromList transition2427Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2427 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1642 = 1 • support1049 := by
  have hs : support1642 = fromList transition2427Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2427Chunk0]
  have hn : (transition2427Raw0 : Multiset ℕ) = 1 • (supportNumbers1049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1049] using hm

private def transition2428Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition2428Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2428Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2428Input0) = fromList transition2428Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2428 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0349 = 1 • support0026 := by
  have hs : support0349 = fromList transition2428Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2428Chunk0]
  have hn : (transition2428Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2429Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition2429Raw0 : List ℕ := [0, 2, 521, 523, 640, 642, 137, 139]
private theorem transition2429Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2429Input0) = fromList transition2429Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2429 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0349 = 1 • support1643 := by
  have hs : support0349 = fromList transition2429Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2429Chunk0]
  have hn : (transition2429Raw0 : Multiset ℕ) = 1 • (supportNumbers1643 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1643] using hm

private def transition2430Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition2430Raw0 : List ℕ := [0, 2, 137, 139]
private theorem transition2430Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2430Input0) = fromList transition2430Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2430 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0349 = 1 • support0026 := by
  have hs : support0349 = fromList transition2430Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2430Chunk0]
  have hn : (transition2430Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition2431Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition2431Raw0 : List ℕ := [0, 2, 681, 683, 544, 546, 137, 139]
private theorem transition2431Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2431Input0) = fromList transition2431Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2431 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0349 = 1 • support1644 := by
  have hs : support0349 = fromList transition2431Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2431Chunk0]
  have hn : (transition2431Raw0 : Multiset ℕ) = 1 • (supportNumbers1644 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1644] using hm

private def transition2432Input0 : List ℕ := [0, 2, 137, 139, 544, 546, 681, 683]
private def transition2432Raw0 : List ℕ := [0, 2, 137, 139, 288, 290, 425, 427]
private theorem transition2432Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2432Input0) = fromList transition2432Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2432 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1644 = 1 • support1488 := by
  have hs : support1644 = fromList transition2432Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2432Chunk0]
  have hn : (transition2432Raw0 : Multiset ℕ) = 1 • (supportNumbers1488 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1488] using hm

private def transition2433Input0 : List ℕ := [0, 2, 137, 139, 544, 546, 681, 683]
private def transition2433Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 288, 864, 290, 866, 425, 1001, 427, 1003]
private theorem transition2433Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2433Input0) = fromList transition2433Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2433 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1644 = 1 • support1489 := by
  have hs : support1644 = fromList transition2433Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2433Chunk0]
  have hn : (transition2433Raw0 : Multiset ℕ) = 1 • (supportNumbers1489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1489] using hm

private def transition2434Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 521, 523, 640, 642, 777, 779, 896, 898]
private def transition2434Raw0 : List ℕ := [0, 2, 137, 139, 0, 2, 137, 139, 265, 267, 384, 386, 265, 267, 384, 386]
private theorem transition2434Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2434Input0) = fromList transition2434Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2434 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0350 = 2 • support0420 := by
  have hs : support0350 = fromList transition2434Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2434Chunk0]
  have hn : (transition2434Raw0 : Multiset ℕ) = 2 • (supportNumbers0420 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0420] using hm

private def transition2435Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 521, 523, 640, 642, 777, 779, 896, 898]
private def transition2435Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 0, 640, 2, 642, 137, 521, 139, 523, 265, 905, 267, 907, 384, 768, 386, 770, 265, 905, 267, 907, 384, 768, 386, 770]
private theorem transition2435Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2435Input0) = fromList transition2435Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2435 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0350 = 2 • support0421 := by
  have hs : support0350 = fromList transition2435Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2435Chunk0]
  have hn : (transition2435Raw0 : Multiset ℕ) = 2 • (supportNumbers0421 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0421] using hm

private def transition2436Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 521, 523, 640, 642, 777, 779, 896, 898]
private def transition2436Raw0 : List ℕ := [0, 2, 137, 139, 0, 2, 137, 139, 265, 267, 384, 386, 265, 267, 384, 386]
private theorem transition2436Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2436Input0) = fromList transition2436Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2436 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0350 = 2 • support0420 := by
  have hs : support0350 = fromList transition2436Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2436Chunk0]
  have hn : (transition2436Raw0 : Multiset ℕ) = 2 • (supportNumbers0420 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0420] using hm

private def transition2437Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 521, 523, 640, 642, 777, 779, 896, 898]
private def transition2437Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 0, 544, 2, 546, 137, 681, 139, 683, 265, 809, 267, 811, 384, 928, 386, 930, 265, 809, 267, 811, 384, 928, 386, 930]
private theorem transition2437Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2437Input0) = fromList transition2437Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2437 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0350 = 2 • support1642 := by
  have hs : support0350 = fromList transition2437Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2437Chunk0]
  have hn : (transition2437Raw0 : Multiset ℕ) = 2 • (supportNumbers1642 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1642] using hm

private def transition2438Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition2438Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition2438Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2438Input0) = fromList transition2438Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2438 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0351 = 1 • support0252 := by
  have hs : support0351 = fromList transition2438Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2438Chunk0]
  have hn : (transition2438Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition2439Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition2439Raw0 : List ℕ := [0, 2, 649, 651, 128, 130, 521, 523]
private theorem transition2439Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2439Input0) = fromList transition2439Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2439 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0351 = 1 • support1645 := by
  have hs : support0351 = fromList transition2439Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2439Chunk0]
  have hn : (transition2439Raw0 : Multiset ℕ) = 1 • (supportNumbers1645 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1645] using hm

private def transition2440Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition2440Raw0 : List ℕ := [0, 2, 128, 130]
private theorem transition2440Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2440Input0) = fromList transition2440Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2440 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0351 = 1 • support0252 := by
  have hs : support0351 = fromList transition2440Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2440Chunk0]
  have hn : (transition2440Raw0 : Multiset ℕ) = 1 • (supportNumbers0252 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0252] using hm

private def transition2441Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition2441Raw0 : List ℕ := [0, 2, 553, 555, 128, 130, 681, 683]
private theorem transition2441Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2441Input0) = fromList transition2441Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2441 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0351 = 1 • support1646 := by
  have hs : support0351 = fromList transition2441Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2441Chunk0]
  have hn : (transition2441Raw0 : Multiset ℕ) = 1 • (supportNumbers1646 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1646] using hm

private def transition2442Input0 : List ℕ := [0, 2, 128, 130, 553, 555, 681, 683]
private def transition2442Raw0 : List ℕ := [0, 2, 128, 130, 297, 299, 425, 427]
private theorem transition2442Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2442Input0) = fromList transition2442Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2442 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1646 = 1 • support1647 := by
  have hs : support1646 = fromList transition2442Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2442Chunk0]
  have hn : (transition2442Raw0 : Multiset ℕ) = 1 • (supportNumbers1647 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1647] using hm

private def transition2443Input0 : List ℕ := [0, 2, 128, 130, 553, 555, 681, 683]
private def transition2443Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 297, 873, 299, 875, 425, 1001, 427, 1003]
private theorem transition2443Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2443Input0) = fromList transition2443Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2443 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1646 = 1 • support1648 := by
  have hs : support1646 = fromList transition2443Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2443Chunk0]
  have hn : (transition2443Raw0 : Multiset ℕ) = 1 • (supportNumbers1648 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1648] using hm

private def transition2444Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 512, 514, 521, 523, 640, 642, 649, 651]
private def transition2444Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private theorem transition2444Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2444Input0) = fromList transition2444Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2444 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0352 = 1 • support0261 := by
  have hs : support0352 = fromList transition2444Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2444Chunk0]
  have hn : (transition2444Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition2445Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 512, 514, 521, 523, 640, 642, 649, 651]
private def transition2445Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 128, 512, 130, 514, 137, 521, 139, 523, 256, 896, 258, 898, 265, 905, 267, 907, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition2445Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2445Input0) = fromList transition2445Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2445 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0352 = 1 • support0262 := by
  have hs : support0352 = fromList transition2445Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2445Chunk0]
  have hn : (transition2445Raw0 : Multiset ℕ) = 1 • (supportNumbers0262 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0262] using hm

private def transition2446Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 512, 514, 521, 523, 640, 642, 649, 651]
private def transition2446Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private theorem transition2446Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2446Input0) = fromList transition2446Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2446 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0352 = 1 • support0261 := by
  have hs : support0352 = fromList transition2446Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2446Chunk0]
  have hn : (transition2446Raw0 : Multiset ℕ) = 1 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition2447Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 512, 514, 521, 523, 640, 642, 649, 651]
private def transition2447Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 128, 672, 130, 674, 137, 681, 139, 683, 256, 800, 258, 802, 265, 809, 267, 811, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition2447Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2447Input0) = fromList transition2447Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2447 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0352 = 1 • support1289 := by
  have hs : support0352 = fromList transition2447Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2447Chunk0]
  have hn : (transition2447Raw0 : Multiset ℕ) = 1 • (supportNumbers1289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1289] using hm

private def transition2448Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition2448Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition2448Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2448Input0) = fromList transition2448Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2448 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0353 = 1 • support0000 := by
  have hs : support0353 = fromList transition2448Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2448Chunk0]
  have hn : (transition2448Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition2449Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition2449Raw0 : List ℕ := [0, 2, 649, 651, 641, 643, 8, 10]
private theorem transition2449Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2449Input0) = fromList transition2449Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2449 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0353 = 1 • support0001 := by
  have hs : support0353 = fromList transition2449Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2449Chunk0]
  have hn : (transition2449Raw0 : Multiset ℕ) = 1 • (supportNumbers0001 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0001] using hm

private def transition2450Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition2450Raw0 : List ℕ := [0, 2, 8, 10]
private theorem transition2450Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2450Input0) = fromList transition2450Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2450 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0353 = 1 • support0000 := by
  have hs : support0353 = fromList transition2450Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2450Chunk0]
  have hn : (transition2450Raw0 : Multiset ℕ) = 1 • (supportNumbers0000 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0000] using hm

private def transition2451Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition2451Raw0 : List ℕ := [0, 2, 553, 555, 545, 547, 8, 10]
private theorem transition2451Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2451Input0) = fromList transition2451Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2451 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0353 = 1 • support1650 := by
  have hs : support0353 = fromList transition2451Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2451Chunk0]
  have hn : (transition2451Raw0 : Multiset ℕ) = 1 • (supportNumbers1650 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1650] using hm

private def transition2452Input0 : List ℕ := [0, 2, 8, 10, 545, 547, 553, 555]
private def transition2452Raw0 : List ℕ := [0, 2, 8, 10, 289, 291, 297, 299]
private theorem transition2452Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2452Input0) = fromList transition2452Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2452 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1650 = 1 • support1651 := by
  have hs : support1650 = fromList transition2452Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2452Chunk0]
  have hn : (transition2452Raw0 : Multiset ℕ) = 1 • (supportNumbers1651 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1651] using hm

private def transition2453Input0 : List ℕ := [0, 2, 8, 10, 545, 547, 553, 555]
private def transition2453Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 289, 865, 291, 867, 297, 873, 299, 875]
private theorem transition2453Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2453Input0) = fromList transition2453Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2453 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1650 = 1 • support1652 := by
  have hs : support1650 = fromList transition2453Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2453Chunk0]
  have hn : (transition2453Raw0 : Multiset ℕ) = 1 • (supportNumbers1652 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1652] using hm

private def transition2454Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 640, 642, 649, 651, 897, 899, 904, 906]
private def transition2454Raw0 : List ℕ := [0, 2, 9, 11, 1, 3, 8, 10, 384, 386, 393, 395, 385, 387, 392, 394]
private theorem transition2454Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2454Input0) = fromList transition2454Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2454 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0354 = 1 • support0281 := by
  have hs : support0354 = fromList transition2454Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2454Chunk0]
  have hn : (transition2454Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition2455Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 640, 642, 649, 651, 897, 899, 904, 906]
private def transition2455Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 1, 641, 3, 643, 8, 648, 10, 650, 384, 768, 386, 770, 393, 777, 395, 779, 385, 769, 387, 771, 392, 776, 394, 778]
private theorem transition2455Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2455Input0) = fromList transition2455Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2455 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0354 = 1 • support0282 := by
  have hs : support0354 = fromList transition2455Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2455Chunk0]
  have hn : (transition2455Raw0 : Multiset ℕ) = 1 • (supportNumbers0282 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0282] using hm

private def transition2456Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 640, 642, 649, 651, 897, 899, 904, 906]
private def transition2456Raw0 : List ℕ := [0, 2, 9, 11, 1, 3, 8, 10, 384, 386, 393, 395, 385, 387, 392, 394]
private theorem transition2456Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2456Input0) = fromList transition2456Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2456 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0354 = 1 • support0281 := by
  have hs : support0354 = fromList transition2456Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2456Chunk0]
  have hn : (transition2456Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition2457Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 640, 642, 649, 651, 897, 899, 904, 906]
private def transition2457Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 1, 545, 3, 547, 8, 552, 10, 554, 384, 928, 386, 930, 393, 937, 395, 939, 385, 929, 387, 931, 392, 936, 394, 938]
private theorem transition2457Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2457Input0) = fromList transition2457Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2457 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0354 = 1 • support1340 := by
  have hs : support0354 = fromList transition2457Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2457Chunk0]
  have hn : (transition2457Raw0 : Multiset ℕ) = 1 • (supportNumbers1340 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1340] using hm

private def transition2458Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition2458Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2458Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2458Input0) = fromList transition2458Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2458 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0355 = 1 • support0065 := by
  have hs : support0355 = fromList transition2458Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2458Chunk0]
  have hn : (transition2458Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2459Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition2459Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2459Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2459Input0) = fromList transition2459Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2459 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0355 = 1 • support0065 := by
  have hs : support0355 = fromList transition2459Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2459Chunk0]
  have hn : (transition2459Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2460Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition2460Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2460Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2460Input0) = fromList transition2460Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2460 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0355 = 1 • support0065 := by
  have hs : support0355 = fromList transition2460Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2460Chunk0]
  have hn : (transition2460Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2461Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition2461Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2461Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2461Input0) = fromList transition2461Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2461 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0355 = 1 • support0065 := by
  have hs : support0355 = fromList transition2461Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2461Chunk0]
  have hn : (transition2461Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2462Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition2462Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2462Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2462Input0) = fromList transition2462Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2462 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0065 = 1 • support0065 := by
  have hs : support0065 = fromList transition2462Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2462Chunk0]
  have hn : (transition2462Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2463Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private def transition2463Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715]
private theorem transition2463Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2463Input0) = fromList transition2463Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2463 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0065 = 1 • support1654 := by
  have hs : support0065 = fromList transition2463Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2463Chunk0]
  have hn : (transition2463Raw0 : Multiset ℕ) = 1 • (supportNumbers1654 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1654] using hm

private def transition2464Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 640, 641, 642, 643, 776, 777, 778, 779]
private def transition2464Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 384, 385, 386, 387, 264, 265, 266, 267]
private theorem transition2464Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2464Input0) = fromList transition2464Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2464 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0356 = 1 • support0108 := by
  have hs : support0356 = fromList transition2464Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2464Chunk0]
  have hn : (transition2464Raw0 : Multiset ℕ) = 1 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition2465Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 640, 641, 642, 643, 776, 777, 778, 779]
private def transition2465Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 136, 520, 137, 521, 138, 522, 139, 523, 384, 768, 385, 769, 386, 770, 387, 771, 264, 904, 265, 905, 266, 906, 267, 907]
private theorem transition2465Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2465Input0) = fromList transition2465Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2465 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0356 = 1 • support0109 := by
  have hs : support0356 = fromList transition2465Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2465Chunk0]
  have hn : (transition2465Raw0 : Multiset ℕ) = 1 • (supportNumbers0109 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0109] using hm

private def transition2466Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 640, 641, 642, 643, 776, 777, 778, 779]
private def transition2466Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 384, 385, 386, 387, 264, 265, 266, 267]
private theorem transition2466Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2466Input0) = fromList transition2466Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2466 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0356 = 1 • support0108 := by
  have hs : support0356 = fromList transition2466Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2466Chunk0]
  have hn : (transition2466Raw0 : Multiset ℕ) = 1 • (supportNumbers0108 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0108] using hm

private def transition2467Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 640, 641, 642, 643, 776, 777, 778, 779]
private def transition2467Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 136, 680, 137, 681, 138, 682, 139, 683, 384, 928, 385, 929, 386, 930, 387, 931, 264, 808, 265, 809, 266, 810, 267, 811]
private theorem transition2467Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2467Input0) = fromList transition2467Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2467 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0356 = 1 • support0830 := by
  have hs : support0356 = fromList transition2467Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2467Chunk0]
  have hn : (transition2467Raw0 : Multiset ℕ) = 1 • (supportNumbers0830 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0830] using hm

private def transition2468Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2468Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition2468Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2468Input0) = fromList transition2468Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2468 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0357 = 1 • support0281 := by
  have hs : support0357 = fromList transition2468Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2468Chunk0]
  have hn : (transition2468Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition2469Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2469Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition2469Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2469Input0) = fromList transition2469Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2469 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0357 = 1 • support0282 := by
  have hs : support0357 = fromList transition2469Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2469Chunk0]
  have hn : (transition2469Raw0 : Multiset ℕ) = 1 • (supportNumbers0282 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0282] using hm

private def transition2470Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2470Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition2470Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2470Input0) = fromList transition2470Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2470 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0357 = 1 • support0281 := by
  have hs : support0357 = fromList transition2470Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2470Chunk0]
  have hn : (transition2470Raw0 : Multiset ℕ) = 1 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition2471Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2471Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition2471Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2471Input0) = fromList transition2471Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2471 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0357 = 1 • support1340 := by
  have hs : support0357 = fromList transition2471Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2471Chunk0]
  have hn : (transition2471Raw0 : Multiset ℕ) = 1 • (supportNumbers1340 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1340] using hm

private def transition2472Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition2472Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition2472Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2472Input0) = fromList transition2472Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2472 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0358 = 1 • support0110 := by
  have hs : support0358 = fromList transition2472Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2472Chunk0]
  have hn : (transition2472Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition2473Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition2473Raw0 : List ℕ := [0, 2, 129, 131, 641, 643, 512, 514]
private theorem transition2473Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2473Input0) = fromList transition2473Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2473 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0358 = 1 • support1656 := by
  have hs : support0358 = fromList transition2473Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2473Chunk0]
  have hn : (transition2473Raw0 : Multiset ℕ) = 1 • (supportNumbers1656 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1656] using hm

private def transition2474Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition2474Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition2474Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2474Input0) = fromList transition2474Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2474 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0358 = 1 • support0110 := by
  have hs : support0358 = fromList transition2474Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2474Chunk0]
  have hn : (transition2474Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
