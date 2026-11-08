import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1849Input0 : List ℕ := [0, 2, 128, 130, 520, 522, 648, 650]
private def transition1849Raw0 : List ℕ := [0, 544, 2, 546, 128, 672, 130, 674, 264, 808, 266, 810, 392, 936, 394, 938]
private theorem transition1849Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1849Input0) = fromList transition1849Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1849 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0257 = 1 • support1483 := by
  have hs : support0257 = fromList transition1849Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1849Chunk0]
  have hn : (transition1849Raw0 : Multiset ℕ) = 1 • (supportNumbers1483 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1483] using hm

private def transition1850Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 544, 546, 672, 674, 808, 810, 936, 938]
private def transition1850Raw0 : List ℕ := [0, 2, 128, 130, 8, 10, 136, 138, 288, 290, 416, 418, 296, 298, 424, 426]
private theorem transition1850Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1850Input0) = fromList transition1850Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1850 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1483 = 1 • support0657 := by
  have hs : support1483 = fromList transition1850Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1850Chunk0]
  have hn : (transition1850Raw0 : Multiset ℕ) = 1 • (supportNumbers0657 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0657] using hm

private def transition1851Input0 : List ℕ := [0, 2, 128, 130, 264, 266, 392, 394, 544, 546, 672, 674, 808, 810, 936, 938]
private def transition1851Raw0 : List ℕ := [0, 576, 2, 578, 128, 704, 130, 706, 8, 584, 10, 586, 136, 712, 138, 714, 288, 864, 290, 866, 416, 992, 418, 994, 296, 872, 298, 874, 424, 1000, 426, 1002]
private theorem transition1851Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1851Input0) = fromList transition1851Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1851 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1483 = 1 • support0658 := by
  have hs : support1483 = fromList transition1851Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1851Chunk0]
  have hn : (transition1851Raw0 : Multiset ℕ) = 1 • (supportNumbers0658 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0658] using hm

private def transition1852Input0 : List ℕ := [0, 2, 649, 651]
private def transition1852Raw0 : List ℕ := [0, 2, 393, 395]
private theorem transition1852Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1852Input0) = fromList transition1852Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1852 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0258 = 1 • support0347 := by
  have hs : support0258 = fromList transition1852Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1852Chunk0]
  have hn : (transition1852Raw0 : Multiset ℕ) = 1 • (supportNumbers0347 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0347] using hm

private def transition1853Input0 : List ℕ := [0, 2, 649, 651]
private def transition1853Raw0 : List ℕ := [0, 640, 2, 642, 393, 777, 395, 779]
private theorem transition1853Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1853Input0) = fromList transition1853Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1853 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0258 = 1 • support0348 := by
  have hs : support0258 = fromList transition1853Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1853Chunk0]
  have hn : (transition1853Raw0 : Multiset ℕ) = 1 • (supportNumbers0348 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0348] using hm

private def transition1854Input0 : List ℕ := [0, 2, 649, 651]
private def transition1854Raw0 : List ℕ := [0, 2, 393, 395]
private theorem transition1854Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1854Input0) = fromList transition1854Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1854 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0258 = 1 • support0347 := by
  have hs : support0258 = fromList transition1854Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1854Chunk0]
  have hn : (transition1854Raw0 : Multiset ℕ) = 1 • (supportNumbers0347 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0347] using hm

private def transition1855Input0 : List ℕ := [0, 2, 393, 395]
private def transition1855Raw0 : List ℕ := [0, 139]
private theorem transition1855Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1855Input0) = fromList transition1855Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1855 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0347 = 1 • support1484 := by
  have hs : support0347 = fromList transition1855Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1855Chunk0]
  have hn : (transition1855Raw0 : Multiset ℕ) = 1 • (supportNumbers1484 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1484] using hm

private def transition1856Input0 : List ℕ := [0, 2, 393, 395]
private def transition1856Raw0 : List ℕ := [0, 578, 713, 139]
private theorem transition1856Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1856Input0) = fromList transition1856Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1856 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0347 = 1 • support1485 := by
  have hs : support0347 = fromList transition1856Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1856Chunk0]
  have hn : (transition1856Raw0 : Multiset ℕ) = 1 • (supportNumbers1485 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1485] using hm

private def transition1857Input0 : List ℕ := [0, 2, 649, 651]
private def transition1857Raw0 : List ℕ := [0, 544, 2, 546, 393, 937, 395, 939]
private theorem transition1857Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1857Input0) = fromList transition1857Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1857 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0258 = 1 • support1487 := by
  have hs : support0258 = fromList transition1857Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1857Chunk0]
  have hn : (transition1857Raw0 : Multiset ℕ) = 1 • (supportNumbers1487 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1487] using hm

private def transition1858Input0 : List ℕ := [0, 2, 393, 395, 544, 546, 937, 939]
private def transition1858Raw0 : List ℕ := [0, 2, 137, 139, 288, 290, 425, 427]
private theorem transition1858Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1858Input0) = fromList transition1858Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1858 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1487 = 1 • support1488 := by
  have hs : support1487 = fromList transition1858Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1858Chunk0]
  have hn : (transition1858Raw0 : Multiset ℕ) = 1 • (supportNumbers1488 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1488] using hm

private def transition1859Input0 : List ℕ := [0, 2, 393, 395, 544, 546, 937, 939]
private def transition1859Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 288, 864, 290, 866, 425, 1001, 427, 1003]
private theorem transition1859Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1859Input0) = fromList transition1859Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1859 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1487 = 1 • support1489 := by
  have hs : support1487 = fromList transition1859Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1859Chunk0]
  have hn : (transition1859Raw0 : Multiset ℕ) = 1 • (supportNumbers1489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1489] using hm

private def transition1860Input0 : List ℕ := [0, 2, 9, 11, 640, 642, 649, 651]
private def transition1860Raw0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private theorem transition1860Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1860Input0) = fromList transition1860Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1860 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0259 = 1 • support0176 := by
  have hs : support0259 = fromList transition1860Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1860Chunk0]
  have hn : (transition1860Raw0 : Multiset ℕ) = 1 • (supportNumbers0176 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0176] using hm

private def transition1861Input0 : List ℕ := [0, 2, 9, 11, 640, 642, 649, 651]
private def transition1861Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition1861Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1861Input0) = fromList transition1861Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1861 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0259 = 1 • support0177 := by
  have hs : support0259 = fromList transition1861Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1861Chunk0]
  have hn : (transition1861Raw0 : Multiset ℕ) = 1 • (supportNumbers0177 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0177] using hm

private def transition1862Input0 : List ℕ := [0, 2, 9, 11, 640, 642, 649, 651]
private def transition1862Raw0 : List ℕ := [0, 2, 9, 11, 384, 386, 393, 395]
private theorem transition1862Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1862Input0) = fromList transition1862Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1862 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0259 = 1 • support0176 := by
  have hs : support0259 = fromList transition1862Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1862Chunk0]
  have hn : (transition1862Raw0 : Multiset ℕ) = 1 • (supportNumbers0176 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0176] using hm

private def transition1863Input0 : List ℕ := [0, 2, 9, 11, 640, 642, 649, 651]
private def transition1863Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition1863Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1863Input0) = fromList transition1863Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1863 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0259 = 1 • support1047 := by
  have hs : support0259 = fromList transition1863Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1863Chunk0]
  have hn : (transition1863Raw0 : Multiset ℕ) = 1 • (supportNumbers1047 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1047] using hm

private def transition1864Input0 : List ℕ := [0, 2, 137, 139, 512, 514, 649, 651]
private def transition1864Raw0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private theorem transition1864Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1864Input0) = fromList transition1864Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1864 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0260 = 1 • support0349 := by
  have hs : support0260 = fromList transition1864Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1864Chunk0]
  have hn : (transition1864Raw0 : Multiset ℕ) = 1 • (supportNumbers0349 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0349] using hm

private def transition1865Input0 : List ℕ := [0, 2, 137, 139, 512, 514, 649, 651]
private def transition1865Raw0 : List ℕ := [0, 640, 2, 642, 137, 521, 139, 523, 256, 896, 258, 898, 393, 777, 395, 779]
private theorem transition1865Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1865Input0) = fromList transition1865Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1865 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0260 = 1 • support0350 := by
  have hs : support0260 = fromList transition1865Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1865Chunk0]
  have hn : (transition1865Raw0 : Multiset ℕ) = 1 • (supportNumbers0350 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0350] using hm

private def transition1866Input0 : List ℕ := [0, 2, 137, 139, 512, 514, 649, 651]
private def transition1866Raw0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private theorem transition1866Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1866Input0) = fromList transition1866Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1866 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0260 = 1 • support0349 := by
  have hs : support0260 = fromList transition1866Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1866Chunk0]
  have hn : (transition1866Raw0 : Multiset ℕ) = 1 • (supportNumbers0349 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0349] using hm

private def transition1867Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition1867Raw0 : List ℕ := [0, 137, 2, 139]
private theorem transition1867Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1867Input0) = fromList transition1867Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1867 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0349 = 1 • support0026 := by
  have hs : support0349 = fromList transition1867Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1867Chunk0]
  have hn : (transition1867Raw0 : Multiset ℕ) = 1 • (supportNumbers0026 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0026] using hm

private def transition1868Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395]
private def transition1868Raw0 : List ℕ := [0, 578, 137, 715, 576, 2, 713, 139]
private theorem transition1868Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1868Input0) = fromList transition1868Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1868 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0349 = 1 • support1491 := by
  have hs : support0349 = fromList transition1868Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1868Chunk0]
  have hn : (transition1868Raw0 : Multiset ℕ) = 1 • (supportNumbers1491 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1491] using hm

private def transition1869Input0 : List ℕ := [0, 2, 137, 139, 512, 514, 649, 651]
private def transition1869Raw0 : List ℕ := [0, 544, 2, 546, 137, 681, 139, 683, 256, 800, 258, 802, 393, 937, 395, 939]
private theorem transition1869Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1869Input0) = fromList transition1869Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1869 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0260 = 1 • support1493 := by
  have hs : support0260 = fromList transition1869Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1869Chunk0]
  have hn : (transition1869Raw0 : Multiset ℕ) = 1 • (supportNumbers1493 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1493] using hm

private def transition1870Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 544, 546, 681, 683, 800, 802, 937, 939]
private def transition1870Raw0 : List ℕ := [0, 2, 137, 139, 0, 2, 137, 139, 288, 290, 425, 427, 288, 290, 425, 427]
private theorem transition1870Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1870Input0) = fromList transition1870Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1870 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1493 = 2 • support1488 := by
  have hs : support1493 = fromList transition1870Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1870Chunk0]
  have hn : (transition1870Raw0 : Multiset ℕ) = 2 • (supportNumbers1488 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1488] using hm

private def transition1871Input0 : List ℕ := [0, 2, 137, 139, 256, 258, 393, 395, 544, 546, 681, 683, 800, 802, 937, 939]
private def transition1871Raw0 : List ℕ := [0, 576, 2, 578, 137, 713, 139, 715, 0, 576, 2, 578, 137, 713, 139, 715, 288, 864, 290, 866, 425, 1001, 427, 1003, 288, 864, 290, 866, 425, 1001, 427, 1003]
private theorem transition1871Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1871Input0) = fromList transition1871Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1871 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1493 = 2 • support1489 := by
  have hs : support1493 = fromList transition1871Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1871Chunk0]
  have hn : (transition1871Raw0 : Multiset ℕ) = 2 • (supportNumbers1489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1489] using hm

private def transition1872Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1872Raw0 : List ℕ := [0, 2, 128, 130, 9, 11, 137, 139]
private theorem transition1872Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1872Input0) = fromList transition1872Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1872 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0261 = 1 • support0351 := by
  have hs : support0261 = fromList transition1872Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1872Chunk0]
  have hn : (transition1872Raw0 : Multiset ℕ) = 1 • (supportNumbers0351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0351] using hm

private def transition1873Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1873Raw0 : List ℕ := [0, 2, 649, 651, 128, 130, 521, 523, 640, 642, 9, 11, 512, 514, 137, 139]
private theorem transition1873Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1873Input0) = fromList transition1873Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1873 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0261 = 1 • support0352 := by
  have hs : support0261 = fromList transition1873Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1873Chunk0]
  have hn : (transition1873Raw0 : Multiset ℕ) = 1 • (supportNumbers0352 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0352] using hm

private def transition1874Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1874Raw0 : List ℕ := [0, 2, 128, 130, 9, 11, 137, 139]
private theorem transition1874Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1874Input0) = fromList transition1874Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1874 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0261 = 1 • support0351 := by
  have hs : support0261 = fromList transition1874Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1874Chunk0]
  have hn : (transition1874Raw0 : Multiset ℕ) = 1 • (supportNumbers0351 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0351] using hm

private def transition1875Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition1875Raw0 : List ℕ := [0, 9, 128, 137]
private theorem transition1875Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1875Input0) = fromList transition1875Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1875 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0351 = 1 • support1494 := by
  have hs : support0351 = fromList transition1875Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1875Chunk0]
  have hn : (transition1875Raw0 : Multiset ℕ) = 1 • (supportNumbers1494 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1494] using hm

private def transition1876Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139]
private def transition1876Raw0 : List ℕ := [0, 578, 9, 587, 128, 706, 137, 715]
private theorem transition1876Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1876Input0) = fromList transition1876Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1876 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0351 = 1 • support1495 := by
  have hs : support0351 = fromList transition1876Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1876Chunk0]
  have hn : (transition1876Raw0 : Multiset ℕ) = 1 • (supportNumbers1495 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1495] using hm

private def transition1877Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395]
private def transition1877Raw0 : List ℕ := [0, 2, 553, 555, 128, 130, 681, 683, 544, 546, 9, 11, 672, 674, 137, 139]
private theorem transition1877Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1877Input0) = fromList transition1877Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1877 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0261 = 1 • support1497 := by
  have hs : support0261 = fromList transition1877Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1877Chunk0]
  have hn : (transition1877Raw0 : Multiset ℕ) = 1 • (supportNumbers1497 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1497] using hm

private def transition1878Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 544, 546, 553, 555, 672, 674, 681, 683]
private def transition1878Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 288, 290, 297, 299, 416, 418, 425, 427]
private theorem transition1878Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1878Input0) = fromList transition1878Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1878 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1497 = 1 • support1048 := by
  have hs : support1497 = fromList transition1878Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1878Chunk0]
  have hn : (transition1878Raw0 : Multiset ℕ) = 1 • (supportNumbers1048 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1048] using hm

private def transition1879Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 544, 546, 553, 555, 672, 674, 681, 683]
private def transition1879Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 128, 704, 130, 706, 137, 713, 139, 715, 288, 864, 290, 866, 297, 873, 299, 875, 416, 992, 418, 994, 425, 1001, 427, 1003]
private theorem transition1879Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1879Input0) = fromList transition1879Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1879 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1497 = 1 • support1049 := by
  have hs : support1497 = fromList transition1879Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1879Chunk0]
  have hn : (transition1879Raw0 : Multiset ℕ) = 1 • (supportNumbers1049 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1049] using hm

private def transition1880Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 512, 514, 521, 523, 640, 642, 649, 651, 768, 770, 777, 779, 896, 898, 905, 907]
private def transition1880Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 256, 258, 265, 267, 384, 386, 393, 395]
private theorem transition1880Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1880Input0) = fromList transition1880Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1880 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0262 = 2 • support0261 := by
  have hs : support0262 = fromList transition1880Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1880Chunk0]
  have hn : (transition1880Raw0 : Multiset ℕ) = 2 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition1881Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 512, 514, 521, 523, 640, 642, 649, 651, 768, 770, 777, 779, 896, 898, 905, 907]
private def transition1881Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 128, 512, 130, 514, 137, 521, 139, 523, 0, 640, 2, 642, 9, 649, 11, 651, 128, 512, 130, 514, 137, 521, 139, 523, 256, 896, 258, 898, 265, 905, 267, 907, 384, 768, 386, 770, 393, 777, 395, 779, 256, 896, 258, 898, 265, 905, 267, 907, 384, 768, 386, 770, 393, 777, 395, 779]
private theorem transition1881Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1881Input0) = fromList transition1881Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1881 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0262 = 2 • support0262 := by
  have hs : support0262 = fromList transition1881Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1881Chunk0]
  have hn : (transition1881Raw0 : Multiset ℕ) = 2 • (supportNumbers0262 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0262] using hm

private def transition1882Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 512, 514, 521, 523, 640, 642, 649, 651, 768, 770, 777, 779, 896, 898, 905, 907]
private def transition1882Raw0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 256, 258, 265, 267, 384, 386, 393, 395]
private theorem transition1882Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1882Input0) = fromList transition1882Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1882 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0262 = 2 • support0261 := by
  have hs : support0262 = fromList transition1882Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1882Chunk0]
  have hn : (transition1882Raw0 : Multiset ℕ) = 2 • (supportNumbers0261 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0261] using hm

private def transition1883Input0 : List ℕ := [0, 2, 9, 11, 128, 130, 137, 139, 256, 258, 265, 267, 384, 386, 393, 395, 512, 514, 521, 523, 640, 642, 649, 651, 768, 770, 777, 779, 896, 898, 905, 907]
private def transition1883Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 128, 672, 130, 674, 137, 681, 139, 683, 0, 544, 2, 546, 9, 553, 11, 555, 128, 672, 130, 674, 137, 681, 139, 683, 256, 800, 258, 802, 265, 809, 267, 811, 384, 928, 386, 930, 393, 937, 395, 939, 256, 800, 258, 802, 265, 809, 267, 811, 384, 928, 386, 930, 393, 937, 395, 939]
private theorem transition1883Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1883Input0) = fromList transition1883Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1883 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0262 = 2 • support1289 := by
  have hs : support0262 = fromList transition1883Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1883Chunk0]
  have hn : (transition1883Raw0 : Multiset ℕ) = 2 • (supportNumbers1289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1289] using hm

private def transition1884Input0 : List ℕ := [0, 2, 9, 11, 513, 515, 520, 522]
private def transition1884Raw0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private theorem transition1884Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1884Input0) = fromList transition1884Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1884 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0263 = 1 • support0353 := by
  have hs : support0263 = fromList transition1884Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1884Chunk0]
  have hn : (transition1884Raw0 : Multiset ℕ) = 1 • (supportNumbers0353 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0353] using hm

private def transition1885Input0 : List ℕ := [0, 2, 9, 11, 513, 515, 520, 522]
private def transition1885Raw0 : List ℕ := [0, 640, 2, 642, 9, 649, 11, 651, 257, 897, 259, 899, 264, 904, 266, 906]
private theorem transition1885Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1885Input0) = fromList transition1885Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1885 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0263 = 1 • support0354 := by
  have hs : support0263 = fromList transition1885Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1885Chunk0]
  have hn : (transition1885Raw0 : Multiset ℕ) = 1 • (supportNumbers0354 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0354] using hm

private def transition1886Input0 : List ℕ := [0, 2, 9, 11, 513, 515, 520, 522]
private def transition1886Raw0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private theorem transition1886Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1886Input0) = fromList transition1886Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1886 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0263 = 1 • support0353 := by
  have hs : support0263 = fromList transition1886Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1886Chunk0]
  have hn : (transition1886Raw0 : Multiset ℕ) = 1 • (supportNumbers0353 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0353] using hm

private def transition1887Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition1887Raw0 : List ℕ := [0, 9, 3, 10]
private theorem transition1887Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1887Input0) = fromList transition1887Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1887 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0353 = 1 • support1498 := by
  have hs : support0353 = fromList transition1887Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1887Chunk0]
  have hn : (transition1887Raw0 : Multiset ℕ) = 1 • (supportNumbers1498 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1498] using hm

private def transition1888Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266]
private def transition1888Raw0 : List ℕ := [0, 578, 9, 587, 577, 3, 584, 10]
private theorem transition1888Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1888Input0) = fromList transition1888Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1888 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0353 = 1 • support1499 := by
  have hs : support0353 = fromList transition1888Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1888Chunk0]
  have hn : (transition1888Raw0 : Multiset ℕ) = 1 • (supportNumbers1499 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1499] using hm

private def transition1889Input0 : List ℕ := [0, 2, 9, 11, 513, 515, 520, 522]
private def transition1889Raw0 : List ℕ := [0, 544, 2, 546, 9, 553, 11, 555, 257, 801, 259, 803, 264, 808, 266, 810]
private theorem transition1889Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1889Input0) = fromList transition1889Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1889 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0263 = 1 • support1501 := by
  have hs : support0263 = fromList transition1889Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1889Chunk0]
  have hn : (transition1889Raw0 : Multiset ℕ) = 1 • (supportNumbers1501 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1501] using hm

private def transition1890Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 544, 546, 553, 555, 801, 803, 808, 810]
private def transition1890Raw0 : List ℕ := [0, 2, 9, 11, 1, 3, 8, 10, 288, 290, 297, 299, 289, 291, 296, 298]
private theorem transition1890Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1890Input0) = fromList transition1890Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1890 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1501 = 1 • support1099 := by
  have hs : support1501 = fromList transition1890Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1890Chunk0]
  have hn : (transition1890Raw0 : Multiset ℕ) = 1 • (supportNumbers1099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1099] using hm

private def transition1891Input0 : List ℕ := [0, 2, 9, 11, 257, 259, 264, 266, 544, 546, 553, 555, 801, 803, 808, 810]
private def transition1891Raw0 : List ℕ := [0, 576, 2, 578, 9, 585, 11, 587, 1, 577, 3, 579, 8, 584, 10, 586, 288, 864, 290, 866, 297, 873, 299, 875, 289, 865, 291, 867, 296, 872, 298, 874]
private theorem transition1891Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1891Input0) = fromList transition1891Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1891 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1501 = 1 • support1100 := by
  have hs : support1501 = fromList transition1891Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1891Chunk0]
  have hn : (transition1891Raw0 : Multiset ℕ) = 1 • (supportNumbers1100 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1100] using hm

private def transition1892Input0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651]
private def transition1892Raw0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private theorem transition1892Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1892Input0) = fromList transition1892Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1892 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0264 = 1 • support0355 := by
  have hs : support0264 = fromList transition1892Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1892Chunk0]
  have hn : (transition1892Raw0 : Multiset ℕ) = 1 • (supportNumbers0355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0355] using hm

private def transition1893Input0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651]
private def transition1893Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1893Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1893Input0) = fromList transition1893Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1893 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0264 = 1 • support0356 := by
  have hs : support0264 = fromList transition1893Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1893Chunk0]
  have hn : (transition1893Raw0 : Multiset ℕ) = 1 • (supportNumbers0356 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0356] using hm

private def transition1894Input0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651]
private def transition1894Raw0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private theorem transition1894Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1894Input0) = fromList transition1894Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1894 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0264 = 1 • support0355 := by
  have hs : support0264 = fromList transition1894Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1894Chunk0]
  have hn : (transition1894Raw0 : Multiset ℕ) = 1 • (supportNumbers0355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0355] using hm

private def transition1895Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition1895Raw0 : List ℕ := [0, 1, 138, 139]
private theorem transition1895Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1895Input0) = fromList transition1895Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1895 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0355 = 1 • support0575 := by
  have hs : support0355 = fromList transition1895Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1895Chunk0]
  have hn : (transition1895Raw0 : Multiset ℕ) = 1 • (supportNumbers0575 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0575] using hm

private def transition1896Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395]
private def transition1896Raw0 : List ℕ := [0, 1, 578, 579, 712, 713, 138, 139]
private theorem transition1896Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1896Input0) = fromList transition1896Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1896 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0355 = 1 • support1502 := by
  have hs : support0355 = fromList transition1896Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1896Chunk0]
  have hn : (transition1896Raw0 : Multiset ℕ) = 1 • (supportNumbers1502 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1502] using hm

private def transition1897Input0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651]
private def transition1897Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1897Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1897Input0) = fromList transition1897Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1897 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0264 = 1 • support1504 := by
  have hs : support0264 = fromList transition1897Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1897Chunk0]
  have hn : (transition1897Raw0 : Multiset ℕ) = 1 • (supportNumbers1504 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1504] using hm

private def transition1898Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 544, 545, 546, 547, 936, 937, 938, 939]
private def transition1898Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 288, 289, 290, 291, 424, 425, 426, 427]
private theorem transition1898Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1898Input0) = fromList transition1898Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1898 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1504 = 1 • support0668 := by
  have hs : support1504 = fromList transition1898Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1898Chunk0]
  have hn : (transition1898Raw0 : Multiset ℕ) = 1 • (supportNumbers0668 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0668] using hm

private def transition1899Input0 : List ℕ := [0, 1, 2, 3, 392, 393, 394, 395, 544, 545, 546, 547, 936, 937, 938, 939]
private def transition1899Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 288, 864, 289, 865, 290, 866, 291, 867, 424, 1000, 425, 1001, 426, 1002, 427, 1003]
private theorem transition1899Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1899Input0) = fromList transition1899Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1899 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1504 = 1 • support0669 := by
  have hs : support1504 = fromList transition1899Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1899Chunk0]
  have hn : (transition1899Raw0 : Multiset ℕ) = 1 • (supportNumbers0669 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0669] using hm

private def transition1900Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1900Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1900Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1900Input0) = fromList transition1900Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1900 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0265 = 1 • support0180 := by
  have hs : support0265 = fromList transition1900Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1900Chunk0]
  have hn : (transition1900Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1901Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1901Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 640, 641, 642, 643, 8, 9, 10, 11]
private theorem transition1901Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1901Input0) = fromList transition1901Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1901 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0265 = 1 • support0357 := by
  have hs : support0265 = fromList transition1901Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1901Chunk0]
  have hn : (transition1901Raw0 : Multiset ℕ) = 1 • (supportNumbers0357 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0357] using hm

private def transition1902Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1902Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition1902Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1902Input0) = fromList transition1902Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1902 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0265 = 1 • support0180 := by
  have hs : support0265 = fromList transition1902Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1902Chunk0]
  have hn : (transition1902Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition1903Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267]
private def transition1903Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 544, 545, 546, 547, 8, 9, 10, 11]
private theorem transition1903Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1903Input0) = fromList transition1903Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1903 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0265 = 1 • support1505 := by
  have hs : support0265 = fromList transition1903Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1903Chunk0]
  have hn : (transition1903Raw0 : Multiset ℕ) = 1 • (supportNumbers1505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1505] using hm

private def transition1904Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 544, 545, 546, 547, 552, 553, 554, 555]
private def transition1904Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 288, 289, 290, 291, 296, 297, 298, 299]
private theorem transition1904Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1904Input0) = fromList transition1904Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1904 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1505 = 1 • support1099 := by
  have hs : support1505 = fromList transition1904Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1904Chunk0]
  have hn : (transition1904Raw0 : Multiset ℕ) = 1 • (supportNumbers1099 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1099] using hm

private def transition1905Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 544, 545, 546, 547, 552, 553, 554, 555]
private def transition1905Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 288, 864, 289, 865, 290, 866, 291, 867, 296, 872, 297, 873, 298, 874, 299, 875]
private theorem transition1905Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1905Input0) = fromList transition1905Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1905 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1505 = 1 • support1100 := by
  have hs : support1505 = fromList transition1905Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1905Chunk0]
  have hn : (transition1905Raw0 : Multiset ℕ) = 1 • (supportNumbers1100 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1100] using hm

private def transition1906Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 640, 641, 642, 643, 648, 649, 650, 651, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1906Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1906Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1906Input0) = fromList transition1906Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1906 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0266 = 2 • support0281 := by
  have hs : support0266 = fromList transition1906Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1906Chunk0]
  have hn : (transition1906Raw0 : Multiset ℕ) = 2 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition1907Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 640, 641, 642, 643, 648, 649, 650, 651, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1907Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1907Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1907Input0) = fromList transition1907Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1907 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0266 = 2 • support0282 := by
  have hs : support0266 = fromList transition1907Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1907Chunk0]
  have hn : (transition1907Raw0 : Multiset ℕ) = 2 • (supportNumbers0282 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0282] using hm

private def transition1908Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 640, 641, 642, 643, 648, 649, 650, 651, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1908Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition1908Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1908Input0) = fromList transition1908Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1908 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0266 = 2 • support0281 := by
  have hs : support0266 = fromList transition1908Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1908Chunk0]
  have hn : (transition1908Raw0 : Multiset ℕ) = 2 • (supportNumbers0281 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0281] using hm

private def transition1909Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 256, 257, 258, 259, 264, 265, 266, 267, 640, 641, 642, 643, 648, 649, 650, 651, 896, 897, 898, 899, 904, 905, 906, 907]
private def transition1909Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1909Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1909Input0) = fromList transition1909Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1909 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0266 = 2 • support1340 := by
  have hs : support0266 = fromList transition1909Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1909Chunk0]
  have hn : (transition1909Raw0 : Multiset ℕ) = 2 • (supportNumbers1340 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1340] using hm

private def transition1910Input0 : List ℕ := [0, 2, 129, 131, 513, 515, 640, 642]
private def transition1910Raw0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private theorem transition1910Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1910Input0) = fromList transition1910Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1910 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0267 = 1 • support0358 := by
  have hs : support0267 = fromList transition1910Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1910Chunk0]
  have hn : (transition1910Raw0 : Multiset ℕ) = 1 • (supportNumbers0358 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0358] using hm

private def transition1911Input0 : List ℕ := [0, 2, 129, 131, 513, 515, 640, 642]
private def transition1911Raw0 : List ℕ := [0, 640, 2, 642, 129, 513, 131, 515, 257, 897, 259, 899, 384, 768, 386, 770]
private theorem transition1911Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1911Input0) = fromList transition1911Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1911 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0267 = 1 • support0359 := by
  have hs : support0267 = fromList transition1911Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1911Chunk0]
  have hn : (transition1911Raw0 : Multiset ℕ) = 1 • (supportNumbers0359 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0359] using hm

private def transition1912Input0 : List ℕ := [0, 2, 129, 131, 513, 515, 640, 642]
private def transition1912Raw0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private theorem transition1912Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1912Input0) = fromList transition1912Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1912 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0267 = 1 • support0358 := by
  have hs : support0267 = fromList transition1912Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1912Chunk0]
  have hn : (transition1912Raw0 : Multiset ℕ) = 1 • (supportNumbers0358 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0358] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
