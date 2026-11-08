import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition2015Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779]
private def transition2015Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 128, 512, 129, 513, 130, 514, 131, 515, 136, 520, 137, 521, 138, 522, 139, 523, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779, 256, 896, 257, 897, 258, 898, 259, 899, 264, 904, 265, 905, 266, 906, 267, 907]
private theorem transition2015Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2015Input0) = fromList transition2015Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2015 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0282 = 1 • support0062 := by
  have hs : support0282 = fromList transition2015Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2015Chunk0]
  have hn : (transition2015Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition2016Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779]
private def transition2016Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139, 384, 385, 386, 387, 392, 393, 394, 395, 256, 257, 258, 259, 264, 265, 266, 267]
private theorem transition2016Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2016Input0) = fromList transition2016Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2016 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0282 = 1 • support0061 := by
  have hs : support0282 = fromList transition2016Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2016Chunk0]
  have hn : (transition2016Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition2017Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 384, 385, 386, 387, 392, 393, 394, 395, 640, 641, 642, 643, 648, 649, 650, 651, 768, 769, 770, 771, 776, 777, 778, 779]
private def transition2017Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 128, 672, 129, 673, 130, 674, 131, 675, 136, 680, 137, 681, 138, 682, 139, 683, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939, 256, 800, 257, 801, 258, 802, 259, 803, 264, 808, 265, 809, 266, 810, 267, 811]
private theorem transition2017Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2017Input0) = fromList transition2017Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2017 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0282 = 1 • support0680 := by
  have hs : support0282 = fromList transition2017Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2017Chunk0]
  have hn : (transition2017Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition2018Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition2018Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition2018Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2018Input0) = fromList transition2018Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2018 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0283 = 1 • support0180 := by
  have hs : support0283 = fromList transition2018Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2018Chunk0]
  have hn : (transition2018Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition2019Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition2019Raw0 : List ℕ := [0, 1, 2, 3, 540, 541, 542, 543, 8, 9, 10, 11, 532, 533, 534, 535]
private theorem transition2019Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2019Input0) = fromList transition2019Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2019 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0283 = 1 • support0372 := by
  have hs : support0283 = fromList transition2019Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2019Chunk0]
  have hn : (transition2019Raw0 : Multiset ℕ) = 1 • (supportNumbers0372 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0372] using hm

private def transition2020Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition2020Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11]
private theorem transition2020Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2020Input0) = fromList transition2020Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2020 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0283 = 1 • support0180 := by
  have hs : support0283 = fromList transition2020Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2020Chunk0]
  have hn : (transition2020Raw0 : Multiset ℕ) = 1 • (supportNumbers0180 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0180] using hm

private def transition2021Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407]
private def transition2021Raw0 : List ℕ := [0, 1, 2, 3, 700, 701, 702, 703, 8, 9, 10, 11, 692, 693, 694, 695]
private theorem transition2021Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2021Input0) = fromList transition2021Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2021 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0283 = 1 • support1531 := by
  have hs : support0283 = fromList transition2021Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2021Chunk0]
  have hn : (transition2021Raw0 : Multiset ℕ) = 1 • (supportNumbers1531 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1531] using hm

private def transition2022Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition2022Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 436, 437, 438, 439, 444, 445, 446, 447]
private theorem transition2022Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2022Input0) = fromList transition2022Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2022 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1531 = 1 • support1532 := by
  have hs : support1531 = fromList transition2022Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2022Chunk0]
  have hn : (transition2022Raw0 : Multiset ℕ) = 1 • (supportNumbers1532 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1532] using hm

private def transition2023Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 692, 693, 694, 695, 700, 701, 702, 703]
private def transition2023Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 444, 1020, 445, 1021, 446, 1022, 447, 1023]
private theorem transition2023Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2023Input0) = fromList transition2023Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2023 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1531 = 1 • support1533 := by
  have hs : support1531 = fromList transition2023Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2023Chunk0]
  have hn : (transition2023Raw0 : Multiset ℕ) = 1 • (supportNumbers1533 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1533] using hm

private def transition2024Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 540, 541, 542, 543, 640, 641, 642, 643, 788, 789, 790, 791, 904, 905, 906, 907]
private def transition2024Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 8, 9, 10, 11, 148, 149, 150, 151, 284, 285, 286, 287, 384, 385, 386, 387, 276, 277, 278, 279, 392, 393, 394, 395]
private theorem transition2024Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2024Input0) = fromList transition2024Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2024 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0284 = 1 • support0288 := by
  have hs : support0284 = fromList transition2024Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2024Chunk0]
  have hn : (transition2024Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition2025Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 540, 541, 542, 543, 640, 641, 642, 643, 788, 789, 790, 791, 904, 905, 906, 907]
private def transition2025Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 156, 540, 157, 541, 158, 542, 159, 543, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 276, 916, 277, 917, 278, 918, 279, 919, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition2025Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2025Input0) = fromList transition2025Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2025 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0284 = 1 • support0289 := by
  have hs : support0284 = fromList transition2025Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2025Chunk0]
  have hn : (transition2025Raw0 : Multiset ℕ) = 1 • (supportNumbers0289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0289] using hm

private def transition2026Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 540, 541, 542, 543, 640, 641, 642, 643, 788, 789, 790, 791, 904, 905, 906, 907]
private def transition2026Raw0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 8, 9, 10, 11, 148, 149, 150, 151, 284, 285, 286, 287, 384, 385, 386, 387, 276, 277, 278, 279, 392, 393, 394, 395]
private theorem transition2026Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2026Input0) = fromList transition2026Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2026 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0284 = 1 • support0288 := by
  have hs : support0284 = fromList transition2026Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2026Chunk0]
  have hn : (transition2026Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition2027Input0 : List ℕ := [0, 1, 2, 3, 156, 157, 158, 159, 264, 265, 266, 267, 404, 405, 406, 407, 540, 541, 542, 543, 640, 641, 642, 643, 788, 789, 790, 791, 904, 905, 906, 907]
private def transition2027Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 156, 700, 157, 701, 158, 702, 159, 703, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 276, 820, 277, 821, 278, 822, 279, 823, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition2027Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2027Input0) = fromList transition2027Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2027 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0284 = 1 • support1355 := by
  have hs : support0284 = fromList transition2027Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2027Chunk0]
  have hn : (transition2027Raw0 : Multiset ℕ) = 1 • (supportNumbers1355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1355] using hm

private def transition2028Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition2028Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2028Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2028Input0) = fromList transition2028Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2028 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition2028Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2028Chunk0]
  have hn : (transition2028Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2029Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition2029Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535]
private theorem transition2029Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2029Input0) = fromList transition2029Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2029 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0199 = 1 • support0373 := by
  have hs : support0199 = fromList transition2029Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2029Chunk0]
  have hn : (transition2029Raw0 : Multiset ℕ) = 1 • (supportNumbers0373 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0373] using hm

private def transition2030Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition2030Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private theorem transition2030Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2030Input0) = fromList transition2030Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2030 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0199 = 1 • support0199 := by
  have hs : support0199 = fromList transition2030Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2030Chunk0]
  have hn : (transition2030Raw0 : Multiset ℕ) = 1 • (supportNumbers0199 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0199] using hm

private def transition2031Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151]
private def transition2031Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695]
private theorem transition2031Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2031Input0) = fromList transition2031Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2031 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0199 = 1 • support1535 := by
  have hs : support0199 = fromList transition2031Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2031Chunk0]
  have hn : (transition2031Raw0 : Multiset ℕ) = 1 • (supportNumbers1535 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1535] using hm

private def transition2032Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 544, 545, 546, 547, 692, 693, 694, 695]
private def transition2032Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 288, 289, 290, 291, 436, 437, 438, 439]
private theorem transition2032Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2032Input0) = fromList transition2032Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2032 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1535 = 1 • support1536 := by
  have hs : support1535 = fromList transition2032Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2032Chunk0]
  have hn : (transition2032Raw0 : Multiset ℕ) = 1 • (supportNumbers1536 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1536] using hm

private def transition2033Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 544, 545, 546, 547, 692, 693, 694, 695]
private def transition2033Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 148, 724, 149, 725, 150, 726, 151, 727, 288, 864, 289, 865, 290, 866, 291, 867, 436, 1012, 437, 1013, 438, 1014, 439, 1015]
private theorem transition2033Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2033Input0) = fromList transition2033Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2033 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1535 = 1 • support1538 := by
  have hs : support1535 = fromList transition2033Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2033Chunk0]
  have hn : (transition2033Raw0 : Multiset ℕ) = 1 • (supportNumbers1538 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1538] using hm

private def transition2034Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition2034Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2034Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2034Input0) = fromList transition2034Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2034 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0285 = 1 • support0374 := by
  have hs : support0285 = fromList transition2034Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2034Chunk0]
  have hn : (transition2034Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2035Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition2035Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2035Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2035Input0) = fromList transition2035Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2035 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0285 = 1 • support0374 := by
  have hs : support0285 = fromList transition2035Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2035Chunk0]
  have hn : (transition2035Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2036Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition2036Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2036Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2036Input0) = fromList transition2036Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2036 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0285 = 1 • support0374 := by
  have hs : support0285 = fromList transition2036Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2036Chunk0]
  have hn : (transition2036Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2037Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2037Raw0 : List ℕ := [0, 1, 28, 29, 136, 137, 148, 149]
private theorem transition2037Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2037Input0) = fromList transition2037Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2037 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0374 = 1 • support1540 := by
  have hs : support0374 = fromList transition2037Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2037Chunk0]
  have hn : (transition2037Raw0 : Multiset ℕ) = 1 • (supportNumbers1540 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1540] using hm

private def transition2038Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2038Raw0 : List ℕ := [0, 1, 578, 579, 28, 29, 606, 607, 136, 137, 714, 715, 148, 149, 726, 727]
private theorem transition2038Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2038Input0) = fromList transition2038Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2038 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0374 = 1 • support1541 := by
  have hs : support0374 = fromList transition2038Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2038Chunk0]
  have hn : (transition2038Raw0 : Multiset ℕ) = 1 • (supportNumbers1541 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1541] using hm

private def transition2039Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395]
private def transition2039Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2039Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2039Input0) = fromList transition2039Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2039 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0285 = 1 • support0374 := by
  have hs : support0285 = fromList transition2039Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2039Chunk0]
  have hn : (transition2039Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2040Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2040Raw0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private theorem transition2040Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition2040Input0) = fromList transition2040Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2040 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0374 = 1 • support0374 := by
  have hs : support0374 = fromList transition2040Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2040Chunk0]
  have hn : (transition2040Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2041Input0 : List ℕ := [0, 1, 2, 3, 28, 29, 30, 31, 136, 137, 138, 139, 148, 149, 150, 151]
private def transition2041Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 28, 604, 29, 605, 30, 606, 31, 607, 136, 712, 137, 713, 138, 714, 139, 715, 148, 724, 149, 725, 150, 726, 151, 727]
private theorem transition2041Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition2041Input0) = fromList transition2041Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2041 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0374 = 1 • support1543 := by
  have hs : support0374 = fromList transition2041Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2041Chunk0]
  have hn : (transition2041Raw0 : Multiset ℕ) = 1 • (supportNumbers1543 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1543] using hm

private def transition2042Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 532, 533, 534, 535, 640, 641, 642, 643, 776, 777, 778, 779, 924, 925, 926, 927]
private def transition2042Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139, 276, 277, 278, 279, 384, 385, 386, 387, 264, 265, 266, 267, 412, 413, 414, 415]
private theorem transition2042Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2042Input0) = fromList transition2042Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2042 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0286 = 1 • support0067 := by
  have hs : support0286 = fromList transition2042Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2042Chunk0]
  have hn : (transition2042Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2043Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 532, 533, 534, 535, 640, 641, 642, 643, 776, 777, 778, 779, 924, 925, 926, 927]
private def transition2043Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 148, 532, 149, 533, 150, 534, 151, 535, 28, 668, 29, 669, 30, 670, 31, 671, 136, 520, 137, 521, 138, 522, 139, 523, 276, 916, 277, 917, 278, 918, 279, 919, 384, 768, 385, 769, 386, 770, 387, 771, 264, 904, 265, 905, 266, 906, 267, 907, 412, 796, 413, 797, 414, 798, 415, 799]
private theorem transition2043Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2043Input0) = fromList transition2043Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2043 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0286 = 1 • support0068 := by
  have hs : support0286 = fromList transition2043Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2043Chunk0]
  have hn : (transition2043Raw0 : Multiset ℕ) = 1 • (supportNumbers0068 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0068] using hm

private def transition2044Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 532, 533, 534, 535, 640, 641, 642, 643, 776, 777, 778, 779, 924, 925, 926, 927]
private def transition2044Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139, 276, 277, 278, 279, 384, 385, 386, 387, 264, 265, 266, 267, 412, 413, 414, 415]
private theorem transition2044Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2044Input0) = fromList transition2044Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2044 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0286 = 1 • support0067 := by
  have hs : support0286 = fromList transition2044Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2044Chunk0]
  have hn : (transition2044Raw0 : Multiset ℕ) = 1 • (supportNumbers0067 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0067] using hm

private def transition2045Input0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 284, 285, 286, 287, 392, 393, 394, 395, 532, 533, 534, 535, 640, 641, 642, 643, 776, 777, 778, 779, 924, 925, 926, 927]
private def transition2045Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 148, 692, 149, 693, 150, 694, 151, 695, 28, 572, 29, 573, 30, 574, 31, 575, 136, 680, 137, 681, 138, 682, 139, 683, 276, 820, 277, 821, 278, 822, 279, 823, 384, 928, 385, 929, 386, 930, 387, 931, 264, 808, 265, 809, 266, 810, 267, 811, 412, 956, 413, 957, 414, 958, 415, 959]
private theorem transition2045Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2045Input0) = fromList transition2045Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2045 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0286 = 1 • support0701 := by
  have hs : support0286 = fromList transition2045Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2045Chunk0]
  have hn : (transition2045Raw0 : Multiset ℕ) = 1 • (supportNumbers0701 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0701] using hm

private def transition2046Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2046Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition2046Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2046Input0) = fromList transition2046Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2046 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0287 = 1 • support0288 := by
  have hs : support0287 = fromList transition2046Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2046Chunk0]
  have hn : (transition2046Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition2047Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2047Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 8, 648, 9, 649, 10, 650, 11, 651, 148, 532, 149, 533, 150, 534, 151, 535, 156, 540, 157, 541, 158, 542, 159, 543, 276, 916, 277, 917, 278, 918, 279, 919, 284, 924, 285, 925, 286, 926, 287, 927, 384, 768, 385, 769, 386, 770, 387, 771, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition2047Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2047Input0) = fromList transition2047Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2047 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0287 = 1 • support0289 := by
  have hs : support0287 = fromList transition2047Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2047Chunk0]
  have hn : (transition2047Raw0 : Multiset ℕ) = 1 • (supportNumbers0289 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0289] using hm

private def transition2048Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2048Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private theorem transition2048Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2048Input0) = fromList transition2048Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2048 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0287 = 1 • support0288 := by
  have hs : support0287 = fromList transition2048Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2048Chunk0]
  have hn : (transition2048Raw0 : Multiset ℕ) = 1 • (supportNumbers0288 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0288] using hm

private def transition2049Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 532, 533, 534, 535, 540, 541, 542, 543, 640, 641, 642, 643, 648, 649, 650, 651]
private def transition2049Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 8, 552, 9, 553, 10, 554, 11, 555, 148, 692, 149, 693, 150, 694, 151, 695, 156, 700, 157, 701, 158, 702, 159, 703, 276, 820, 277, 821, 278, 822, 279, 823, 284, 828, 285, 829, 286, 830, 287, 831, 384, 928, 385, 929, 386, 930, 387, 931, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition2049Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition2049Input0) = fromList transition2049Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2049 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0287 = 1 • support1355 := by
  have hs : support0287 = fromList transition2049Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2049Chunk0]
  have hn : (transition2049Raw0 : Multiset ℕ) = 1 • (supportNumbers1355 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1355] using hm

private def transition2050Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2050Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2050Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition2050Input0) = fromList transition2050Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2050 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0288 = 1 • support0374 := by
  have hs : support0288 = fromList transition2050Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2050Chunk0]
  have hn : (transition2050Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm

private def transition2051Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2051Raw0 : List ℕ := [0, 1, 2, 3, 648, 649, 650, 651, 148, 149, 150, 151, 540, 541, 542, 543, 660, 661, 662, 663, 28, 29, 30, 31, 512, 513, 514, 515, 136, 137, 138, 139]
private theorem transition2051Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition2051Input0) = fromList transition2051Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2051 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0288 = 1 • support0375 := by
  have hs : support0288 = fromList transition2051Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2051Chunk0]
  have hn : (transition2051Raw0 : Multiset ℕ) = 1 • (supportNumbers0375 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0375] using hm

private def transition2052Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 148, 149, 150, 151, 156, 157, 158, 159, 276, 277, 278, 279, 284, 285, 286, 287, 384, 385, 386, 387, 392, 393, 394, 395]
private def transition2052Raw0 : List ℕ := [0, 1, 2, 3, 148, 149, 150, 151, 28, 29, 30, 31, 136, 137, 138, 139]
private theorem transition2052Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition2052Input0) = fromList transition2052Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition2052 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0288 = 1 • support0374 := by
  have hs : support0288 = fromList transition2052Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition2052Chunk0]
  have hn : (transition2052Raw0 : Multiset ℕ) = 1 • (supportNumbers0374 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0374] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
