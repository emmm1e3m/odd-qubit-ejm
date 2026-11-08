import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2079Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 648, 649, 650, 651, 668, 669, 670, 671]
private def transition2079Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 392, 936, 393, 937, 394, 938, 395, 939, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2079Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2079Input0) = fromList transition2079Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2079 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0292 = 1 • support1557 := by
  have hs : support0292 = fromList transition2079Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2079Chunk0]
  have hn : (transition2079Raw0 : Multiset ℕ) = 1 • (supportNumbers1557 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1557] using hm

private def transition2080Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition2080Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 136, 137, 138, 139, 156, 157, 158, 159, 288, 289, 290, 291, 308, 309, 310, 311, 424, 425, 426, 427, 444, 445, 446, 447]
private theorem transition2080Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2080Input0) = fromList transition2080Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2080 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1557 = 1 • support0712 := by
  have hs : support1557 = fromList transition2080Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2080Chunk0]
  have hn : (transition2080Raw0 : Multiset ℕ) = 1 • (supportNumbers0712 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0712] using hm

private def transition2081Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 392, 393, 394, 395, 412, 413, 414, 415, 544, 545, 546, 547, 564, 565, 566, 567, 936, 937, 938, 939, 956, 957, 958, 959]
private def transition2081Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 20, 596, 21, 597, 22, 598, 23, 599, 136, 712, 137, 713, 138, 714, 139, 715, 156, 732, 157, 733, 158, 734, 159, 735, 288, 864, 289, 865, 290, 866, 291, 867, 308, 884, 309, 885, 310, 886, 311, 887, 424, 1000, 425, 1001, 426, 1002, 427, 1003, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2081Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2081Input0) = fromList transition2081Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2081 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1557 = 1 • support0714 := by
  have hs : support1557 = fromList transition2081Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2081Chunk0]
  have hn : (transition2081Raw0 : Multiset ℕ) = 1 • (supportNumbers0714 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0714] using hm

private def transition2082Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition2082Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2082Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2082Input0) = fromList transition2082Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2082 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0293 = 1 • support0014 := by
  have hs : support0293 = fromList transition2082Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2082Chunk0]
  have hn : (transition2082Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition2083Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition2083Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2083Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2083Input0) = fromList transition2083Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2083 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0293 = 1 • support0015 := by
  have hs : support0293 = fromList transition2083Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2083Chunk0]
  have hn : (transition2083Raw0 : Multiset ℕ) = 1 • (supportNumbers0015 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0015] using hm

private def transition2084Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition2084Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2084Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2084Input0) = fromList transition2084Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2084 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0293 = 1 • support0014 := by
  have hs : support0293 = fromList transition2084Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2084Chunk0]
  have hn : (transition2084Raw0 : Multiset ℕ) = 1 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition2085Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671]
private def transition2085Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2085Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2085Input0) = fromList transition2085Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2085 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0293 = 1 • support0505 := by
  have hs : support0293 = fromList transition2085Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2085Chunk0]
  have hn : (transition2085Raw0 : Multiset ℕ) = 1 • (supportNumbers0505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0505] using hm

private def transition2086Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2086Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition2086Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2086Input0) = fromList transition2086Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2086 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0294 = 1 • support0204 := by
  have hs : support0294 = fromList transition2086Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2086Chunk0]
  have hn : (transition2086Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition2087Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2087Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 20, 21, 22, 23, 668, 669, 670, 671, 640, 641, 642, 643, 8, 9, 10, 11, 660, 661, 662, 663, 28, 29, 30, 31]
private theorem transition2087Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2087Input0) = fromList transition2087Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2087 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0294 = 1 • support0293 := by
  have hs : support0294 = fromList transition2087Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2087Chunk0]
  have hn : (transition2087Raw0 : Multiset ℕ) = 1 • (supportNumbers0293 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0293] using hm

private def transition2088Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2088Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 8, 9, 10, 11, 28, 29, 30, 31]
private theorem transition2088Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2088Input0) = fromList transition2088Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2088 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0294 = 1 • support0204 := by
  have hs : support0294 = fromList transition2088Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2088Chunk0]
  have hn : (transition2088Raw0 : Multiset ℕ) = 1 • (supportNumbers0204 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0204] using hm

private def transition2089Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287]
private def transition2089Raw0 : List ℕ := [0, 1, 2, 3, 552, 553, 554, 555, 20, 21, 22, 23, 572, 573, 574, 575, 544, 545, 546, 547, 8, 9, 10, 11, 564, 565, 566, 567, 28, 29, 30, 31]
private theorem transition2089Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2089Input0) = fromList transition2089Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2089 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0294 = 1 • support1368 := by
  have hs : support0294 = fromList transition2089Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2089Chunk0]
  have hn : (transition2089Raw0 : Multiset ℕ) = 1 • (supportNumbers1368 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1368] using hm

private def transition2090Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2090Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2090Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2090Input0) = fromList transition2090Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2090 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0295 = 2 • support0014 := by
  have hs : support0295 = fromList transition2090Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2090Chunk0]
  have hn : (transition2090Raw0 : Multiset ℕ) = 2 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition2091Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2091Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 404, 788, 405, 789, 406, 790, 407, 791, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2091Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2091Input0) = fromList transition2091Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2091 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0295 = 2 • support0015 := by
  have hs : support0295 = fromList transition2091Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2091Chunk0]
  have hn : (transition2091Raw0 : Multiset ℕ) = 2 • (supportNumbers0015 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0015] using hm

private def transition2092Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2092Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415, 384, 385, 386, 387, 392, 393, 394, 395, 404, 405, 406, 407, 412, 413, 414, 415]
private theorem transition2092Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2092Input0) = fromList transition2092Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2092 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0295 = 2 • support0014 := by
  have hs : support0295 = fromList transition2092Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2092Chunk0]
  have hn : (transition2092Raw0 : Multiset ℕ) = 2 • (supportNumbers0014 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0014] using hm

private def transition2093Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 256, 257, 258, 259, 264, 265, 266, 267, 276, 277, 278, 279, 284, 285, 286, 287, 640, 641, 642, 643, 648, 649, 650, 651, 660, 661, 662, 663, 668, 669, 670, 671, 896, 897, 898, 899, 904, 905, 906, 907, 916, 917, 918, 919, 924, 925, 926, 927]
private def transition2093Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 20, 564, 21, 565, 22, 566, 23, 567, 28, 572, 29, 573, 30, 574, 31, 575, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 404, 948, 405, 949, 406, 950, 407, 951, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2093Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2093Input0) = fromList transition2093Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2093 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0295 = 2 • support0505 := by
  have hs : support0295 = fromList transition2093Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2093Chunk0]
  have hn : (transition2093Raw0 : Multiset ℕ) = 2 • (supportNumbers0505 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0505] using hm

private def transition2094Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition2094Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2094Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2094Input0) = fromList transition2094Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2094 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0296 = 1 • support0377 := by
  have hs : support0296 = fromList transition2094Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2094Chunk0]
  have hn : (transition2094Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2095Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition2095Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 20, 660, 21, 661, 22, 662, 23, 663, 128, 512, 129, 513, 130, 514, 131, 515, 148, 532, 149, 533, 150, 534, 151, 535, 256, 896, 257, 897, 258, 898, 259, 899, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 404, 788, 405, 789, 406, 790, 407, 791]
private theorem transition2095Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2095Input0) = fromList transition2095Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2095 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0296 = 1 • support0378 := by
  have hs : support0296 = fromList transition2095Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2095Chunk0]
  have hn : (transition2095Raw0 : Multiset ℕ) = 1 • (supportNumbers0378 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0378] using hm

private def transition2096Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition2096Raw0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 256, 257, 258, 259, 276, 277, 278, 279, 384, 385, 386, 387, 404, 405, 406, 407]
private theorem transition2096Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2096Input0) = fromList transition2096Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2096 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0296 = 1 • support0377 := by
  have hs : support0296 = fromList transition2096Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2096Chunk0]
  have hn : (transition2096Raw0 : Multiset ℕ) = 1 • (supportNumbers0377 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0377] using hm

private def transition2097Input0 : List ℕ := [0, 1, 2, 3, 20, 21, 22, 23, 128, 129, 130, 131, 148, 149, 150, 151, 512, 513, 514, 515, 532, 533, 534, 535, 640, 641, 642, 643, 660, 661, 662, 663]
private def transition2097Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 20, 564, 21, 565, 22, 566, 23, 567, 128, 672, 129, 673, 130, 674, 131, 675, 148, 692, 149, 693, 150, 694, 151, 695, 256, 800, 257, 801, 258, 802, 259, 803, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 404, 948, 405, 949, 406, 950, 407, 951]
private theorem transition2097Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2097Input0) = fromList transition2097Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2097 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0296 = 1 • support1553 := by
  have hs : support0296 = fromList transition2097Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2097Chunk0]
  have hn : (transition2097Raw0 : Multiset ℕ) = 1 • (supportNumbers1553 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1553] using hm

private def transition2098Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition2098Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition2098Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2098Input0) = fromList transition2098Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2098 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0073 = 1 • support0073 := by
  have hs : support0073 = fromList transition2098Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2098Chunk0]
  have hn : (transition2098Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm

private def transition2099Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition2099Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 20, 660, 21, 661, 22, 662, 23, 663, 28, 668, 29, 669, 30, 670, 31, 671, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543]
private theorem transition2099Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2099Input0) = fromList transition2099Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2099 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0073 = 1 • support0074 := by
  have hs : support0073 = fromList transition2099Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2099Chunk0]
  have hn : (transition2099Raw0 : Multiset ℕ) = 1 • (supportNumbers0074 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0074] using hm

private def transition2100Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private def transition2100Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 20, 21, 22, 23, 28, 29, 30, 31, 128, 129, 130, 131, 136, 137, 138, 139, 148, 149, 150, 151, 156, 157, 158, 159]
private theorem transition2100Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2100Input0) = fromList transition2100Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2100 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0073 = 1 • support0073 := by
  have hs : support0073 = fromList transition2100Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2100Chunk0]
  have hn : (transition2100Raw0 : Multiset ℕ) = 1 • (supportNumbers0073 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0073] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
