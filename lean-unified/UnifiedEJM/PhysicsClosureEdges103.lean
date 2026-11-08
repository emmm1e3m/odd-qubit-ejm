import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1769Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 640, 641, 642, 643, 644, 645, 646, 647, 656, 657, 658, 659, 660, 661, 662, 663, 704, 705, 706, 707, 708, 709, 710, 711, 720, 721, 722, 723, 724, 725, 726, 727]
private def transition1769Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 4, 548, 5, 549, 6, 550, 7, 551, 16, 560, 17, 561, 18, 562, 19, 563, 20, 564, 21, 565, 22, 566, 23, 567, 64, 608, 65, 609, 66, 610, 67, 611, 68, 612, 69, 613, 70, 614, 71, 615, 80, 624, 81, 625, 82, 626, 83, 627, 84, 628, 85, 629, 86, 630, 87, 631, 384, 928, 385, 929, 386, 930, 387, 931, 388, 932, 389, 933, 390, 934, 391, 935, 400, 944, 401, 945, 402, 946, 403, 947, 404, 948, 405, 949, 406, 950, 407, 951, 448, 992, 449, 993, 450, 994, 451, 995, 452, 996, 453, 997, 454, 998, 455, 999, 464, 1008, 465, 1009, 466, 1010, 467, 1011, 468, 1012, 469, 1013, 470, 1014, 471, 1015]
private theorem transition1769Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1769Input0) = fromList transition1769Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1769 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0245 = 1 • support1463 := by
  have hs : support0245 = fromList transition1769Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1769Chunk0]
  have hn : (transition1769Raw0 : Multiset ℕ) = 1 • (supportNumbers1463 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1463] using hm

private def transition1770Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition1770Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 128, 129, 130, 131, 132, 133, 134, 135, 144, 145, 146, 147, 148, 149, 150, 151, 192, 193, 194, 195, 196, 197, 198, 199, 208, 209, 210, 211, 212, 213, 214, 215]
private theorem transition1770Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1770Input0) = fromList transition1770Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1770Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition1770Raw1 : List ℕ := [288, 289, 290, 291, 292, 293, 294, 295, 304, 305, 306, 307, 308, 309, 310, 311, 352, 353, 354, 355, 356, 357, 358, 359, 368, 369, 370, 371, 372, 373, 374, 375, 416, 417, 418, 419, 420, 421, 422, 423, 432, 433, 434, 435, 436, 437, 438, 439, 480, 481, 482, 483, 484, 485, 486, 487, 496, 497, 498, 499, 500, 501, 502, 503]
private theorem transition1770Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1770Input1) = fromList transition1770Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1770 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1463 = 1 • support1464 := by
  have hs : support1463 = fromList transition1770Input0 + fromList transition1770Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1770Chunk0, transition1770Chunk1]
  have hn : (transition1770Raw0 : Multiset ℕ) + (transition1770Raw1 : Multiset ℕ) = 1 • (supportNumbers1464 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1464] using hm

private def transition1771Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 384, 385, 386, 387, 388, 389, 390, 391, 400, 401, 402, 403, 404, 405, 406, 407, 448, 449, 450, 451, 452, 453, 454, 455, 464, 465, 466, 467, 468, 469, 470, 471]
private def transition1771Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 128, 704, 129, 705, 130, 706, 131, 707, 132, 708, 133, 709, 134, 710, 135, 711, 144, 720, 145, 721, 146, 722, 147, 723, 148, 724, 149, 725, 150, 726, 151, 727, 192, 640, 193, 641, 194, 642, 195, 643, 196, 644, 197, 645, 198, 646, 199, 647, 208, 656, 209, 657, 210, 658, 211, 659, 212, 660, 213, 661, 214, 662, 215, 663]
private theorem transition1771Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1771Input0) = fromList transition1771Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

private def transition1771Input1 : List ℕ := [544, 545, 546, 547, 548, 549, 550, 551, 560, 561, 562, 563, 564, 565, 566, 567, 608, 609, 610, 611, 612, 613, 614, 615, 624, 625, 626, 627, 628, 629, 630, 631, 928, 929, 930, 931, 932, 933, 934, 935, 944, 945, 946, 947, 948, 949, 950, 951, 992, 993, 994, 995, 996, 997, 998, 999, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015]
private def transition1771Raw1 : List ℕ := [288, 864, 289, 865, 290, 866, 291, 867, 292, 868, 293, 869, 294, 870, 295, 871, 304, 880, 305, 881, 306, 882, 307, 883, 308, 884, 309, 885, 310, 886, 311, 887, 352, 800, 353, 801, 354, 802, 355, 803, 356, 804, 357, 805, 358, 806, 359, 807, 368, 816, 369, 817, 370, 818, 371, 819, 372, 820, 373, 821, 374, 822, 375, 823, 416, 992, 417, 993, 418, 994, 419, 995, 420, 996, 421, 997, 422, 998, 423, 999, 432, 1008, 433, 1009, 434, 1010, 435, 1011, 436, 1012, 437, 1013, 438, 1014, 439, 1015, 480, 928, 481, 929, 482, 930, 483, 931, 484, 932, 485, 933, 486, 934, 487, 935, 496, 944, 497, 945, 498, 946, 499, 947, 500, 948, 501, 949, 502, 950, 503, 951]
private theorem transition1771Chunk1 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1771Input1) = fromList transition1771Raw1 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1771 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1463 = 1 • support1466 := by
  have hs : support1463 = fromList transition1771Input0 + fromList transition1771Input1 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1771Chunk0, transition1771Chunk1]
  have hn : (transition1771Raw0 : Multiset ℕ) + (transition1771Raw1 : Multiset ℕ) = 1 • (supportNumbers1466 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1466] using hm

private def transition1772Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1772Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition1772Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1772Input0) = fromList transition1772Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1772 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0246 = 1 • support0092 := by
  have hs : support0246 = fromList transition1772Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1772Chunk0]
  have hn : (transition1772Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition1773Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1773Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 648, 649, 650, 651, 652, 653, 654, 655, 16, 17, 18, 19, 20, 21, 22, 23, 664, 665, 666, 667, 668, 669, 670, 671, 64, 65, 66, 67, 68, 69, 70, 71, 712, 713, 714, 715, 716, 717, 718, 719, 80, 81, 82, 83, 84, 85, 86, 87, 728, 729, 730, 731, 732, 733, 734, 735]
private theorem transition1773Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1773Input0) = fromList transition1773Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1773 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0246 = 1 • support0339 := by
  have hs : support0246 = fromList transition1773Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1773Chunk0]
  have hn : (transition1773Raw0 : Multiset ℕ) = 1 • (supportNumbers0339 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0339] using hm

private def transition1774Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1774Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87]
private theorem transition1774Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1774Input0) = fromList transition1774Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1774 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0246 = 1 • support0092 := by
  have hs : support0246 = fromList transition1774Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1774Chunk0]
  have hn : (transition1774Raw0 : Multiset ℕ) = 1 • (supportNumbers0092 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0092] using hm

private def transition1775Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1775Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 552, 553, 554, 555, 556, 557, 558, 559, 16, 17, 18, 19, 20, 21, 22, 23, 568, 569, 570, 571, 572, 573, 574, 575, 64, 65, 66, 67, 68, 69, 70, 71, 616, 617, 618, 619, 620, 621, 622, 623, 80, 81, 82, 83, 84, 85, 86, 87, 632, 633, 634, 635, 636, 637, 638, 639]
private theorem transition1775Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1775Input0) = fromList transition1775Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1775 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0246 = 1 • support1468 := by
  have hs : support0246 = fromList transition1775Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1775Chunk0]
  have hn : (transition1775Raw0 : Multiset ℕ) = 1 • (supportNumbers1468 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1468] using hm

private def transition1776Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 552, 553, 554, 555, 556, 557, 558, 559, 568, 569, 570, 571, 572, 573, 574, 575, 616, 617, 618, 619, 620, 621, 622, 623, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition1776Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 296, 297, 298, 299, 300, 301, 302, 303, 312, 313, 314, 315, 316, 317, 318, 319, 360, 361, 362, 363, 364, 365, 366, 367, 376, 377, 378, 379, 380, 381, 382, 383]
private theorem transition1776Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1776Input0) = fromList transition1776Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1776 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1468 = 1 • support1469 := by
  have hs : support1468 = fromList transition1776Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1776Chunk0]
  have hn : (transition1776Raw0 : Multiset ℕ) = 1 • (supportNumbers1469 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1469] using hm

private def transition1777Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 64, 65, 66, 67, 68, 69, 70, 71, 80, 81, 82, 83, 84, 85, 86, 87, 552, 553, 554, 555, 556, 557, 558, 559, 568, 569, 570, 571, 572, 573, 574, 575, 616, 617, 618, 619, 620, 621, 622, 623, 632, 633, 634, 635, 636, 637, 638, 639]
private def transition1777Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 4, 580, 5, 581, 6, 582, 7, 583, 16, 592, 17, 593, 18, 594, 19, 595, 20, 596, 21, 597, 22, 598, 23, 599, 64, 512, 65, 513, 66, 514, 67, 515, 68, 516, 69, 517, 70, 518, 71, 519, 80, 528, 81, 529, 82, 530, 83, 531, 84, 532, 85, 533, 86, 534, 87, 535, 296, 872, 297, 873, 298, 874, 299, 875, 300, 876, 301, 877, 302, 878, 303, 879, 312, 888, 313, 889, 314, 890, 315, 891, 316, 892, 317, 893, 318, 894, 319, 895, 360, 808, 361, 809, 362, 810, 363, 811, 364, 812, 365, 813, 366, 814, 367, 815, 376, 824, 377, 825, 378, 826, 379, 827, 380, 828, 381, 829, 382, 830, 383, 831]
private theorem transition1777Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1777Input0) = fromList transition1777Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1777 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1468 = 1 • support1471 := by
  have hs : support1468 = fromList transition1777Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1777Chunk0]
  have hn : (transition1777Raw0 : Multiset ℕ) = 1 • (supportNumbers1471 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1471] using hm

private def transition1778Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1778Raw0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private theorem transition1778Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1778Input0) = fromList transition1778Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1778 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0246 = 1 • support0246 := by
  have hs : support0246 = fromList transition1778Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1778Chunk0]
  have hn : (transition1778Raw0 : Multiset ℕ) = 1 • (supportNumbers0246 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0246] using hm

private def transition1779Input0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95]
private def transition1779Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 4, 644, 5, 645, 6, 646, 7, 647, 8, 648, 9, 649, 10, 650, 11, 651, 12, 652, 13, 653, 14, 654, 15, 655, 16, 656, 17, 657, 18, 658, 19, 659, 20, 660, 21, 661, 22, 662, 23, 663, 24, 664, 25, 665, 26, 666, 27, 667, 28, 668, 29, 669, 30, 670, 31, 671, 64, 704, 65, 705, 66, 706, 67, 707, 68, 708, 69, 709, 70, 710, 71, 711, 72, 712, 73, 713, 74, 714, 75, 715, 76, 716, 77, 717, 78, 718, 79, 719, 80, 720, 81, 721, 82, 722, 83, 723, 84, 724, 85, 725, 86, 726, 87, 727, 88, 728, 89, 729, 90, 730, 91, 731, 92, 732, 93, 733, 94, 734, 95, 735]
private theorem transition1779Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1779Input0) = fromList transition1779Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1779 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0246 = 1 • support0340 := by
  have hs : support0246 = fromList transition1779Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1779Chunk0]
  have hn : (transition1779Raw0 : Multiset ℕ) = 1 • (supportNumbers0340 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0340] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
