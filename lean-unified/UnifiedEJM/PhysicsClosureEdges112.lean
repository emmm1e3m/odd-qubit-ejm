import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1969Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 512, 513, 514, 515, 640, 641, 642, 643, 768, 769, 770, 771, 896, 897, 898, 899]
private def transition1969Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 256, 800, 257, 801, 258, 802, 259, 803, 384, 928, 385, 929, 386, 930, 387, 931, 256, 800, 257, 801, 258, 802, 259, 803, 384, 928, 385, 929, 386, 930, 387, 931]
private theorem transition1969Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1969Input0) = fromList transition1969Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1969 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0274 = 2 • support1323 := by
  have hs : support0274 = fromList transition1969Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1969Chunk0]
  have hn : (transition1969Raw0 : Multiset ℕ) = 2 • (supportNumbers1323 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1323] using hm

private def transition1970Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1970Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1970Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1970Input0) = fromList transition1970Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1970 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0275 = 1 • support0012 := by
  have hs : support0275 = fromList transition1970Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1970Chunk0]
  have hn : (transition1970Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1971Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1971Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1971Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1971Input0) = fromList transition1971Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1971 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0275 = 1 • support0012 := by
  have hs : support0275 = fromList transition1971Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1971Chunk0]
  have hn : (transition1971Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1972Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1972Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1972Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1972Input0) = fromList transition1972Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1972 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0275 = 1 • support0012 := by
  have hs : support0275 = fromList transition1972Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1972Chunk0]
  have hn : (transition1972Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1973Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287]
private def transition1973Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1973Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1973Input0) = fromList transition1973Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1973 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0275 = 1 • support0012 := by
  have hs : support0275 = fromList transition1973Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1973Chunk0]
  have hn : (transition1973Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1974Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition1974Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1974Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1974Input0) = fromList transition1974Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1974 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0012 = 1 • support0012 := by
  have hs : support0012 = fromList transition1974Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1974Chunk0]
  have hn : (transition1974Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1975Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private def transition1975Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607]
private theorem transition1975Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1975Input0) = fromList transition1975Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1975 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0012 = 1 • support1331 := by
  have hs : support0012 = fromList transition1975Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1975Chunk0]
  have hn : (transition1975Raw0 : Multiset ℕ) = 1 • (supportNumbers1331 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1331] using hm

private def transition1976Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 640, 641, 642, 643, 924, 925, 926, 927]
private def transition1976Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1976Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1976Input0) = fromList transition1976Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1976 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0276 = 1 • support0367 := by
  have hs : support0276 = fromList transition1976Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1976Chunk0]
  have hn : (transition1976Raw0 : Multiset ℕ) = 1 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition1977Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 640, 641, 642, 643, 924, 925, 926, 927]
private def transition1977Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition1977Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1977Input0) = fromList transition1977Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1977 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0276 = 1 • support0368 := by
  have hs : support0276 = fromList transition1977Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1977Chunk0]
  have hn : (transition1977Raw0 : Multiset ℕ) = 1 • (supportNumbers0368 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0368] using hm

private def transition1978Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 640, 641, 642, 643, 924, 925, 926, 927]
private def transition1978Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1978Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1978Input0) = fromList transition1978Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1978 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0276 = 1 • support0367 := by
  have hs : support0276 = fromList transition1978Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1978Chunk0]
  have hn : (transition1978Raw0 : Multiset ℕ) = 1 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition1979Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1979Raw0 : List ℕ := [0, 1, 28, 29, 130, 131, 158, 159]
private theorem transition1979Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1979Input0) = fromList transition1979Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1979 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0367 = 1 • support1518 := by
  have hs : support0367 = fromList transition1979Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1979Chunk0]
  have hn : (transition1979Raw0 : Multiset ℕ) = 1 • (supportNumbers1518 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1518] using hm

private def transition1980Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415]
private def transition1980Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 704, 705, 130, 131, 732, 733, 158, 159]
private theorem transition1980Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1980Input0) = fromList transition1980Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1980 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0367 = 1 • support1519 := by
  have hs : support0367 = fromList transition1980Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1980Chunk0]
  have hn : (transition1980Raw0 : Multiset ℕ) = 1 • (supportNumbers1519 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1519] using hm

private def transition1981Input0 : List ℕ := [0, 1, 2, 3, 284, 285, 286, 287, 640, 641, 642, 643, 924, 925, 926, 927]
private def transition1981Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition1981Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1981Input0) = fromList transition1981Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1981 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0276 = 1 • support1521 := by
  have hs : support0276 = fromList transition1981Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1981Chunk0]
  have hn : (transition1981Raw0 : Multiset ℕ) = 1 • (supportNumbers1521 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1521] using hm

private def transition1982Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition1982Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 288, 289, 290, 291, 316, 317, 318, 319, 416, 417, 418, 419, 444, 445, 446, 447]
private theorem transition1982Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1982Input0) = fromList transition1982Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1982 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1521 = 1 • support0861 := by
  have hs : support1521 = fromList transition1982Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1982Chunk0]
  have hn : (transition1982Raw0 : Multiset ℕ) = 1 • (supportNumbers0861 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0861] using hm

private def transition1983Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 544, 545, 546, 547, 572, 573, 574, 575, 928, 929, 930, 931, 956, 957, 958, 959]
private def transition1983Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 128, 704, 129, 705, 130, 706, 131, 707, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895, 416, 992, 417, 993, 418, 994, 419, 995, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition1983Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1983Input0) = fromList transition1983Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1983 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1521 = 1 • support0863 := by
  have hs : support1521 = fromList transition1983Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1983Chunk0]
  have hn : (transition1983Raw0 : Multiset ℕ) = 1 • (supportNumbers0863 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0863] using hm

private def transition1984Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1984Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1984Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1984Input0) = fromList transition1984Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1984 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0277 = 1 • support0012 := by
  have hs : support0277 = fromList transition1984Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1984Chunk0]
  have hn : (transition1984Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1985Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1985Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 640, 641, 642, 643, 28, 29, 30, 31]
private theorem transition1985Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1985Input0) = fromList transition1985Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1985 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0277 = 1 • support0369 := by
  have hs : support0277 = fromList transition1985Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1985Chunk0]
  have hn : (transition1985Raw0 : Multiset ℕ) = 1 • (supportNumbers0369 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0369] using hm

private def transition1986Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1986Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31]
private theorem transition1986Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1986Input0) = fromList transition1986Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1986 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0277 = 1 • support0012 := by
  have hs : support0277 = fromList transition1986Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1986Chunk0]
  have hn : (transition1986Raw0 : Multiset ℕ) = 1 • (supportNumbers0012 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0012] using hm

private def transition1987Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287]
private def transition1987Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 544, 545, 546, 547, 28, 29, 30, 31]
private theorem transition1987Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1987Input0) = fromList transition1987Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1987 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0277 = 1 • support1522 := by
  have hs : support0277 = fromList transition1987Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1987Chunk0]
  have hn : (transition1987Raw0 : Multiset ℕ) = 1 • (supportNumbers1522 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1522] using hm

private def transition1988Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 544, 545, 546, 547, 572, 573, 574, 575]
private def transition1988Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 288, 289, 290, 291, 316, 317, 318, 319]
private theorem transition1988Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1988Input0) = fromList transition1988Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1988 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1522 = 1 • support1328 := by
  have hs : support1522 = fromList transition1988Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1988Chunk0]
  have hn : (transition1988Raw0 : Multiset ℕ) = 1 • (supportNumbers1328 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1328] using hm

private def transition1989Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 544, 545, 546, 547, 572, 573, 574, 575]
private def transition1989Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 288, 864, 289, 865, 290, 866, 291, 867, 316, 892, 317, 893, 318, 894, 319, 895]
private theorem transition1989Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1989Input0) = fromList transition1989Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1989 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1522 = 1 • support1329 := by
  have hs : support1522 = fromList transition1989Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1989Chunk0]
  have hn : (transition1989Raw0 : Multiset ℕ) = 1 • (supportNumbers1329 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1329] using hm

private def transition1990Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 640, 641, 642, 643, 668, 669, 670, 671, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1990Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1990Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1990Input0) = fromList transition1990Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1990 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0278 = 2 • support0367 := by
  have hs : support0278 = fromList transition1990Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1990Chunk0]
  have hn : (transition1990Raw0 : Multiset ℕ) = 2 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition1991Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 640, 641, 642, 643, 668, 669, 670, 671, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1991Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition1991Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1991Input0) = fromList transition1991Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1991 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0278 = 2 • support0368 := by
  have hs : support0278 = fromList transition1991Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1991Chunk0]
  have hn : (transition1991Raw0 : Multiset ℕ) = 2 • (supportNumbers0368 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0368] using hm

private def transition1992Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 640, 641, 642, 643, 668, 669, 670, 671, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1992Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 0, 1, 2, 3, 28, 29, 30, 31, 384, 385, 386, 387, 412, 413, 414, 415, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition1992Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1992Input0) = fromList transition1992Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1992 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0278 = 2 • support0367 := by
  have hs : support0278 = fromList transition1992Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1992Chunk0]
  have hn : (transition1992Raw0 : Multiset ℕ) = 2 • (supportNumbers0367 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0367] using hm

private def transition1993Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 256, 257, 258, 259, 284, 285, 286, 287, 640, 641, 642, 643, 668, 669, 670, 671, 896, 897, 898, 899, 924, 925, 926, 927]
private def transition1993Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition1993Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1993Input0) = fromList transition1993Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1993 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0278 = 2 • support1521 := by
  have hs : support0278 = fromList transition1993Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1993Chunk0]
  have hn : (transition1993Raw0 : Multiset ℕ) = 2 • (supportNumbers1521 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1521] using hm

private def transition1994Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1994Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1994Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1994Input0) = fromList transition1994Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1994 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0279 = 1 • support0187 := by
  have hs : support0279 = fromList transition1994Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1994Chunk0]
  have hn : (transition1994Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1995Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1995Raw0 : List ℕ := [0, 1, 2, 3, 668, 669, 670, 671, 128, 129, 130, 131, 540, 541, 542, 543]
private theorem transition1995Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1995Input0) = fromList transition1995Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1995 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0279 = 1 • support0370 := by
  have hs : support0279 = fromList transition1995Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1995Chunk0]
  have hn : (transition1995Raw0 : Multiset ℕ) = 1 • (supportNumbers0370 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0370] using hm

private def transition1996Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1996Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1996Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1996Input0) = fromList transition1996Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1996 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0279 = 1 • support0187 := by
  have hs : support0279 = fromList transition1996Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1996Chunk0]
  have hn : (transition1996Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1997Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159]
private def transition1997Raw0 : List ℕ := [0, 1, 2, 3, 572, 573, 574, 575, 128, 129, 130, 131, 700, 701, 702, 703]
private theorem transition1997Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1997Input0) = fromList transition1997Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1997 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0279 = 1 • support1523 := by
  have hs : support0279 = fromList transition1997Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1997Chunk0]
  have hn : (transition1997Raw0 : Multiset ℕ) = 1 • (supportNumbers1523 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1523] using hm

private def transition1998Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 572, 573, 574, 575, 700, 701, 702, 703]
private def transition1998Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 316, 317, 318, 319, 444, 445, 446, 447]
private theorem transition1998Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1998Input0) = fromList transition1998Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1998 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1523 = 1 • support1524 := by
  have hs : support1523 = fromList transition1998Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1998Chunk0]
  have hn : (transition1998Raw0 : Multiset ℕ) = 1 • (supportNumbers1524 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1524] using hm

private def transition1999Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 572, 573, 574, 575, 700, 701, 702, 703]
private def transition1999Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 316, 892, 317, 893, 318, 894, 319, 895, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition1999Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1999Input0) = fromList transition1999Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1999 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1523 = 1 • support1525 := by
  have hs : support1523 = fromList transition1999Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1999Chunk0]
  have hn : (transition1999Raw0 : Multiset ℕ) = 1 • (supportNumbers1525 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1525] using hm

private def transition2000Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2000Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2000Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2000Input0) = fromList transition2000Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2000 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0280 = 1 • support0194 := by
  have hs : support0280 = fromList transition2000Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2000Chunk0]
  have hn : (transition2000Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2001Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2001Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 156, 540, 157, 541, 158, 542, 159, 543, 256, 896, 257, 897, 258, 898, 259, 899, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2001Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2001Input0) = fromList transition2001Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2001 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0280 = 1 • support0195 := by
  have hs : support0280 = fromList transition2001Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2001Chunk0]
  have hn : (transition2001Raw0 : Multiset ℕ) = 1 • (supportNumbers0195 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0195] using hm

private def transition2002Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2002Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 256, 257, 258, 259, 284, 285, 286, 287, 384, 385, 386, 387, 412, 413, 414, 415]
private theorem transition2002Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2002Input0) = fromList transition2002Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2002 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0280 = 1 • support0194 := by
  have hs : support0280 = fromList transition2002Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2002Chunk0]
  have hn : (transition2002Raw0 : Multiset ℕ) = 1 • (supportNumbers0194 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0194] using hm

private def transition2003Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 128, 129, 130, 131, 156, 157, 158, 159, 512, 513, 514, 515, 540, 541, 542, 543, 640, 641, 642, 643, 668, 669, 670, 671]
private def transition2003Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 28, 572, 29, 573, 30, 574, 31, 575, 128, 672, 129, 673, 130, 674, 131, 675, 156, 700, 157, 701, 158, 702, 159, 703, 256, 800, 257, 801, 258, 802, 259, 803, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2003Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2003Input0) = fromList transition2003Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2003 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0280 = 1 • support1095 := by
  have hs : support0280 = fromList transition2003Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2003Chunk0]
  have hn : (transition2003Raw0 : Multiset ℕ) = 1 • (supportNumbers1095 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1095] using hm

private def transition2004Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition2004Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition2004Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2004Input0) = fromList transition2004Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2004 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0180 = 1 • support0180 := by
  have hs : support0180 = fromList transition2004Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2004Chunk0]
  have hn : (transition2004Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition2005Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition2005Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651]
private theorem transition2005Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2005Input0) = fromList transition2005Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2005 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0180 = 1 • support0357 := by
  have hs : support0180 = fromList transition2005Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2005Chunk0]
  have hn : (transition2005Raw0 : Multiset ℕ) = 1 • (supportNumbers0357 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0357] using hm

private def transition2006Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition2006Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition2006Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2006Input0) = fromList transition2006Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2006 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0180 = 1 • support0180 := by
  have hs : support0180 = fromList transition2006Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2006Chunk0]
  have hn : (transition2006Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition2007Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private def transition2007Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555]
private theorem transition2007Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2007Input0) = fromList transition2007Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2007 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0180 = 1 • support1505 := by
  have hs : support0180 = fromList transition2007Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2007Chunk0]
  have hn : (transition2007Raw0 : Multiset ℕ) = 1 • (supportNumbers1505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1505] using hm

private def transition2008Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2008Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2008Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2008Input0) = fromList transition2008Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2008 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0281 = 1 • support0065 := by
  have hs : support0281 = fromList transition2008Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2008Chunk0]
  have hn : (transition2008Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2009Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2009Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 512, 513, 514, 515, 136, 137, 138, 139]
private theorem transition2009Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2009Input0) = fromList transition2009Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2009 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0281 = 1 • support0371 := by
  have hs : support0281 = fromList transition2009Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2009Chunk0]
  have hn : (transition2009Raw0 : Multiset ℕ) = 1 • (supportNumbers0371 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0371] using hm

private def transition2010Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2010Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139]
private theorem transition2010Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2010Input0) = fromList transition2010Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2010 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0281 = 1 • support0065 := by
  have hs : support0281 = fromList transition2010Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2010Chunk0]
  have hn : (transition2010Raw0 : Multiset ℕ) = 1 • (supportNumbers0065 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0065] using hm

private def transition2011Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2011Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 672, 673, 674, 675, 136, 137, 138, 139]
private theorem transition2011Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2011Input0) = fromList transition2011Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2011 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0281 = 1 • support1527 := by
  have hs : support0281 = fromList transition2011Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2011Chunk0]
  have hn : (transition2011Raw0 : Multiset ℕ) = 1 • (supportNumbers1527 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1527] using hm

private def transition2012Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 552, 553, 554, 555, 672, 673, 674, 675]
private def transition2012Raw0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 296, 297, 298, 299, 416, 417, 418, 419]
private theorem transition2012Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2012Input0) = fromList transition2012Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2012 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1527 = 1 • support1528 := by
  have hs : support1527 = fromList transition2012Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2012Chunk0]
  have hn : (transition2012Raw0 : Multiset ℕ) = 1 • (supportNumbers1528 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1528] using hm

private def transition2013Input0 : List ℕ := [0, 1, 2, 3, 136, 137, 138, 139, 552, 553, 554, 555, 672, 673, 674, 675]
private def transition2013Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 136, 712, 137, 713, 138, 714, 139, 715, 296, 872, 297, 873, 298, 874, 299, 875, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition2013Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2013Input0) = fromList transition2013Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2013 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1527 = 1 • support1529 := by
  have hs : support1527 = fromList transition2013Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2013Chunk0]
  have hn : (transition2013Raw0 : Multiset ℕ) = 1 • (supportNumbers1529 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1529] using hm

private def transition2014Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779]
private def transition2014Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267]
private theorem transition2014Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2014Input0) = fromList transition2014Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2014 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0282 = 1 • support0061 := by
  have hs : support0282 = fromList transition2014Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2014Chunk0]
  have hn : (transition2014Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
