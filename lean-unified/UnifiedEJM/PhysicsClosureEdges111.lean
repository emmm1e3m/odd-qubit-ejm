import UnifiedEJM.PhysicsClosureSupports
import UnifiedEJM.PhysicsSparseNumbers

namespace UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
open UnifiedEJM.WeightedTransfer.SparseCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def transition1913Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition1913Raw0 : List ℕ := [0, 129, 3, 130]
private theorem transition1913Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1913Input0) = fromList transition1913Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1913 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0358 = 1 • support1506 := by
  have hs : support0358 = fromList transition1913Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1913Chunk0]
  have hn : (transition1913Raw0 : Multiset ℕ) = 1 • (supportNumbers1506 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1506] using hm

private def transition1914Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386]
private def transition1914Raw0 : List ℕ := [0, 578, 129, 707, 577, 3, 704, 130]
private theorem transition1914Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1914Input0) = fromList transition1914Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1914 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0358 = 1 • support1507 := by
  have hs : support0358 = fromList transition1914Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1914Chunk0]
  have hn : (transition1914Raw0 : Multiset ℕ) = 1 • (supportNumbers1507 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1507] using hm

private def transition1915Input0 : List ℕ := [0, 2, 129, 131, 513, 515, 640, 642]
private def transition1915Raw0 : List ℕ := [0, 544, 2, 546, 129, 673, 131, 675, 257, 801, 259, 803, 384, 928, 386, 930]
private theorem transition1915Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1915Input0) = fromList transition1915Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1915 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0267 = 1 • support1509 := by
  have hs : support0267 = fromList transition1915Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1915Chunk0]
  have hn : (transition1915Raw0 : Multiset ℕ) = 1 • (supportNumbers1509 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1509] using hm

private def transition1916Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 544, 546, 673, 675, 801, 803, 928, 930]
private def transition1916Raw0 : List ℕ := [0, 2, 129, 131, 1, 3, 128, 130, 288, 290, 417, 419, 289, 291, 416, 418]
private theorem transition1916Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1916Input0) = fromList transition1916Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1916 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1509 = 1 • support1081 := by
  have hs : support1509 = fromList transition1916Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1916Chunk0]
  have hn : (transition1916Raw0 : Multiset ℕ) = 1 • (supportNumbers1081 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1081] using hm

private def transition1917Input0 : List ℕ := [0, 2, 129, 131, 257, 259, 384, 386, 544, 546, 673, 675, 801, 803, 928, 930]
private def transition1917Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 1, 577, 3, 579, 128, 704, 130, 706, 288, 864, 290, 866, 417, 993, 419, 995, 289, 865, 291, 867, 416, 992, 418, 994]
private theorem transition1917Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1917Input0) = fromList transition1917Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1917 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1509 = 1 • support1082 := by
  have hs : support1509 = fromList transition1917Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1917Chunk0]
  have hn : (transition1917Raw0 : Multiset ℕ) = 1 • (supportNumbers1082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1082] using hm

private def transition1918Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1918Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition1918Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1918Input0) = fromList transition1918Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1918 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0268 = 1 • support0110 := by
  have hs : support0268 = fromList transition1918Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1918Chunk0]
  have hn : (transition1918Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition1919Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1919Raw0 : List ℕ := [0, 2, 648, 650, 129, 131, 521, 523]
private theorem transition1919Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1919Input0) = fromList transition1919Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1919 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0268 = 1 • support0360 := by
  have hs : support0268 = fromList transition1919Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1919Chunk0]
  have hn : (transition1919Raw0 : Multiset ℕ) = 1 • (supportNumbers0360 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0360] using hm

private def transition1920Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1920Raw0 : List ℕ := [0, 2, 129, 131]
private theorem transition1920Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1920Input0) = fromList transition1920Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1920 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0268 = 1 • support0110 := by
  have hs : support0268 = fromList transition1920Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1920Chunk0]
  have hn : (transition1920Raw0 : Multiset ℕ) = 1 • (supportNumbers0110 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0110] using hm

private def transition1921Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1921Raw0 : List ℕ := [0, 2, 552, 554, 129, 131, 681, 683]
private theorem transition1921Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1921Input0) = fromList transition1921Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1921 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0268 = 1 • support1510 := by
  have hs : support0268 = fromList transition1921Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1921Chunk0]
  have hn : (transition1921Raw0 : Multiset ℕ) = 1 • (supportNumbers1510 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1510] using hm

private def transition1922Input0 : List ℕ := [0, 2, 129, 131, 552, 554, 681, 683]
private def transition1922Raw0 : List ℕ := [0, 2, 129, 131, 296, 298, 425, 427]
private theorem transition1922Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1922Input0) = fromList transition1922Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1922 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1510 = 1 • support1511 := by
  have hs : support1510 = fromList transition1922Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1922Chunk0]
  have hn : (transition1922Raw0 : Multiset ℕ) = 1 • (supportNumbers1511 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1511] using hm

private def transition1923Input0 : List ℕ := [0, 2, 129, 131, 552, 554, 681, 683]
private def transition1923Raw0 : List ℕ := [0, 576, 2, 578, 129, 705, 131, 707, 296, 872, 298, 874, 425, 1001, 427, 1003]
private theorem transition1923Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1923Input0) = fromList transition1923Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1923 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1510 = 1 • support1512 := by
  have hs : support1510 = fromList transition1923Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1923Chunk0]
  have hn : (transition1923Raw0 : Multiset ℕ) = 1 • (supportNumbers1512 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1512] using hm

private def transition1924Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1924Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem transition1924Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1924Input0) = fromList transition1924Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1924 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0268 = 1 • support0268 := by
  have hs : support0268 = fromList transition1924Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1924Chunk0]
  have hn : (transition1924Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1925Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1925Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523]
private theorem transition1925Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1925Input0) = fromList transition1925Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1925 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0268 = 1 • support0361 := by
  have hs : support0268 = fromList transition1925Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1925Chunk0]
  have hn : (transition1925Raw0 : Multiset ℕ) = 1 • (supportNumbers0361 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0361] using hm

private def transition1926Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1926Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private theorem transition1926Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1926Input0) = fromList transition1926Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1926 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0268 = 1 • support0268 := by
  have hs : support0268 = fromList transition1926Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1926Chunk0]
  have hn : (transition1926Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1927Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139]
private def transition1927Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683]
private theorem transition1927Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1927Input0) = fromList transition1927Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1927 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0268 = 1 • support1514 := by
  have hs : support0268 = fromList transition1927Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1927Chunk0]
  have hn : (transition1927Raw0 : Multiset ℕ) = 1 • (supportNumbers1514 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1514] using hm

private def transition1928Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 544, 546, 552, 554, 673, 675, 681, 683]
private def transition1928Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 288, 290, 296, 298, 417, 419, 425, 427]
private theorem transition1928Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1928Input0) = fromList transition1928Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1928 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1514 = 1 • support0489 := by
  have hs : support1514 = fromList transition1928Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1928Chunk0]
  have hn : (transition1928Raw0 : Multiset ℕ) = 1 • (supportNumbers0489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0489] using hm

private def transition1929Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 544, 546, 552, 554, 673, 675, 681, 683]
private def transition1929Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 288, 864, 290, 866, 296, 872, 298, 874, 417, 993, 419, 995, 425, 1001, 427, 1003]
private theorem transition1929Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1929Input0) = fromList transition1929Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1929 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1514 = 1 • support0490 := by
  have hs : support1514 = fromList transition1929Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1929Chunk0]
  have hn : (transition1929Raw0 : Multiset ℕ) = 1 • (supportNumbers0490 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0490] using hm

private def transition1930Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 512, 514, 520, 522, 641, 643, 649, 651]
private def transition1930Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private theorem transition1930Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1930Input0) = fromList transition1930Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1930 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0269 = 1 • support0362 := by
  have hs : support0269 = fromList transition1930Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1930Chunk0]
  have hn : (transition1930Raw0 : Multiset ℕ) = 1 • (supportNumbers0362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0362] using hm

private def transition1931Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 512, 514, 520, 522, 641, 643, 649, 651]
private def transition1931Raw0 : List ℕ := [0, 640, 2, 642, 8, 648, 10, 650, 129, 513, 131, 515, 137, 521, 139, 523, 256, 896, 258, 898, 264, 904, 266, 906, 385, 769, 387, 771, 393, 777, 395, 779]
private theorem transition1931Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1931Input0) = fromList transition1931Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1931 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0269 = 1 • support0363 := by
  have hs : support0269 = fromList transition1931Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1931Chunk0]
  have hn : (transition1931Raw0 : Multiset ℕ) = 1 • (supportNumbers0363 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0363] using hm

private def transition1932Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 512, 514, 520, 522, 641, 643, 649, 651]
private def transition1932Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private theorem transition1932Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1932Input0) = fromList transition1932Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1932 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0269 = 1 • support0362 := by
  have hs : support0269 = fromList transition1932Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1932Chunk0]
  have hn : (transition1932Raw0 : Multiset ℕ) = 1 • (supportNumbers0362 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0362] using hm

private def transition1933Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition1933Raw0 : List ℕ := [0, 8, 129, 137, 2, 10, 131, 139]
private theorem transition1933Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1933Input0) = fromList transition1933Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1933 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0362 = 1 • support0268 := by
  have hs : support0362 = fromList transition1933Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1933Chunk0]
  have hn : (transition1933Raw0 : Multiset ℕ) = 1 • (supportNumbers0268 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0268] using hm

private def transition1934Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395]
private def transition1934Raw0 : List ℕ := [0, 578, 8, 586, 129, 707, 137, 715, 576, 2, 584, 10, 705, 131, 713, 139]
private theorem transition1934Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1934Input0) = fromList transition1934Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1934 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0362 = 1 • support1308 := by
  have hs : support0362 = fromList transition1934Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1934Chunk0]
  have hn : (transition1934Raw0 : Multiset ℕ) = 1 • (supportNumbers1308 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1308] using hm

private def transition1935Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 512, 514, 520, 522, 641, 643, 649, 651]
private def transition1935Raw0 : List ℕ := [0, 544, 2, 546, 8, 552, 10, 554, 129, 673, 131, 675, 137, 681, 139, 683, 256, 800, 258, 802, 264, 808, 266, 810, 385, 929, 387, 931, 393, 937, 395, 939]
private theorem transition1935Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1935Input0) = fromList transition1935Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1935 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0269 = 1 • support1515 := by
  have hs : support0269 = fromList transition1935Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1935Chunk0]
  have hn : (transition1935Raw0 : Multiset ℕ) = 1 • (supportNumbers1515 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1515] using hm

private def transition1936Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 544, 546, 552, 554, 673, 675, 681, 683, 800, 802, 808, 810, 929, 931, 937, 939]
private def transition1936Raw0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 0, 2, 8, 10, 129, 131, 137, 139, 288, 290, 296, 298, 417, 419, 425, 427, 288, 290, 296, 298, 417, 419, 425, 427]
private theorem transition1936Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1936Input0) = fromList transition1936Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1936 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1515 = 2 • support0489 := by
  have hs : support1515 = fromList transition1936Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1936Chunk0]
  have hn : (transition1936Raw0 : Multiset ℕ) = 2 • (supportNumbers0489 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0489] using hm

private def transition1937Input0 : List ℕ := [0, 2, 8, 10, 129, 131, 137, 139, 256, 258, 264, 266, 385, 387, 393, 395, 544, 546, 552, 554, 673, 675, 681, 683, 800, 802, 808, 810, 929, 931, 937, 939]
private def transition1937Raw0 : List ℕ := [0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 0, 576, 2, 578, 8, 584, 10, 586, 129, 705, 131, 707, 137, 713, 139, 715, 288, 864, 290, 866, 296, 872, 298, 874, 417, 993, 419, 995, 425, 1001, 427, 1003, 288, 864, 290, 866, 296, 872, 298, 874, 417, 993, 419, 995, 425, 1001, 427, 1003]
private theorem transition1937Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1937Input0) = fromList transition1937Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1937 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1515 = 2 • support0490 := by
  have hs : support1515 = fromList transition1937Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1937Chunk0]
  have hn : (transition1937Raw0 : Multiset ℕ) = 2 • (supportNumbers0490 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0490] using hm

private def transition1938Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1938Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1938Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1938Input0) = fromList transition1938Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1938 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1938Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1938Chunk0]
  have hn : (transition1938Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1939Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1939Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515]
private theorem transition1939Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1939Input0) = fromList transition1939Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1939 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0187 = 1 • support0364 := by
  have hs : support0187 = fromList transition1939Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1939Chunk0]
  have hn : (transition1939Raw0 : Multiset ℕ) = 1 • (supportNumbers0364 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0364] using hm

private def transition1940Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1940Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1940Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1940Input0) = fromList transition1940Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1940 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0187 = 1 • support0187 := by
  have hs : support0187 = fromList transition1940Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1940Chunk0]
  have hn : (transition1940Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1941Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private def transition1941Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675]
private theorem transition1941Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1941Input0) = fromList transition1941Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1941 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0187 = 1 • support1516 := by
  have hs : support0187 = fromList transition1941Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1941Chunk0]
  have hn : (transition1941Raw0 : Multiset ℕ) = 1 • (supportNumbers1516 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1516] using hm

private def transition1942Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 544, 545, 546, 547, 672, 673, 674, 675]
private def transition1942Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 288, 289, 290, 291, 416, 417, 418, 419]
private theorem transition1942Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1942Input0) = fromList transition1942Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1942 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1516 = 1 • support1081 := by
  have hs : support1516 = fromList transition1942Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1942Chunk0]
  have hn : (transition1942Raw0 : Multiset ℕ) = 1 • (supportNumbers1081 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1081] using hm

private def transition1943Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 544, 545, 546, 547, 672, 673, 674, 675]
private def transition1943Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 128, 704, 129, 705, 130, 706, 131, 707, 288, 864, 289, 865, 290, 866, 291, 867, 416, 992, 417, 993, 418, 994, 419, 995]
private theorem transition1943Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1943Input0) = fromList transition1943Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1943 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1516 = 1 • support1082 := by
  have hs : support1516 = fromList transition1943Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1943Chunk0]
  have hn : (transition1943Raw0 : Multiset ℕ) = 1 • (supportNumbers1082 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1082] using hm

private def transition1944Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1944Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition1944Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1944Input0) = fromList transition1944Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1944 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0270 = 1 • support0114 := by
  have hs : support0270 = fromList transition1944Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1944Chunk0]
  have hn : (transition1944Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition1945Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1945Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition1945Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1945Input0) = fromList transition1945Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1945 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0270 = 1 • support0114 := by
  have hs : support0270 = fromList transition1945Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1945Chunk0]
  have hn : (transition1945Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition1946Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1946Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition1946Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1946Input0) = fromList transition1946Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1946 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0270 = 1 • support0114 := by
  have hs : support0270 = fromList transition1946Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1946Chunk0]
  have hn : (transition1946Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition1947Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395]
private def transition1947Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139]
private theorem transition1947Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1947Input0) = fromList transition1947Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1947 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0270 = 1 • support0114 := by
  have hs : support0270 = fromList transition1947Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1947Chunk0]
  have hn : (transition1947Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition1948Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition1948Raw0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private theorem transition1948Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1948Input0) = fromList transition1948Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1948 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support0114 = 1 • support0114 := by
  have hs : support0114 = fromList transition1948Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1948Chunk0]
  have hn : (transition1948Raw0 : Multiset ℕ) = 1 • (supportNumbers0114 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0114] using hm

private def transition1949Input0 : List ℕ := [0, 1, 2, 3, 8, 9, 10, 11, 128, 129, 130, 131, 136, 137, 138, 139]
private def transition1949Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 8, 584, 9, 585, 10, 586, 11, 587, 128, 704, 129, 705, 130, 706, 131, 707, 136, 712, 137, 713, 138, 714, 139, 715]
private theorem transition1949Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1949Input0) = fromList transition1949Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1949 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support0114 = 1 • support0678 := by
  have hs : support0114 = fromList transition1949Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1949Chunk0]
  have hn : (transition1949Raw0 : Multiset ℕ) = 1 • (supportNumbers0678 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0678] using hm

private def transition1950Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 512, 513, 514, 515, 640, 641, 642, 643, 776, 777, 778, 779, 904, 905, 906, 907]
private def transition1950Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139, 256, 257, 258, 259, 384, 385, 386, 387, 264, 265, 266, 267, 392, 393, 394, 395]
private theorem transition1950Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1950Input0) = fromList transition1950Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1950 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0271 = 1 • support0061 := by
  have hs : support0271 = fromList transition1950Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1950Chunk0]
  have hn : (transition1950Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition1951Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 512, 513, 514, 515, 640, 641, 642, 643, 776, 777, 778, 779, 904, 905, 906, 907]
private def transition1951Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 8, 648, 9, 649, 10, 650, 11, 651, 136, 520, 137, 521, 138, 522, 139, 523, 256, 896, 257, 897, 258, 898, 259, 899, 384, 768, 385, 769, 386, 770, 387, 771, 264, 904, 265, 905, 266, 906, 267, 907, 392, 776, 393, 777, 394, 778, 395, 779]
private theorem transition1951Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1951Input0) = fromList transition1951Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1951 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0271 = 1 • support0062 := by
  have hs : support0271 = fromList transition1951Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1951Chunk0]
  have hn : (transition1951Raw0 : Multiset ℕ) = 1 • (supportNumbers0062 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0062] using hm

private def transition1952Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 512, 513, 514, 515, 640, 641, 642, 643, 776, 777, 778, 779, 904, 905, 906, 907]
private def transition1952Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 8, 9, 10, 11, 136, 137, 138, 139, 256, 257, 258, 259, 384, 385, 386, 387, 264, 265, 266, 267, 392, 393, 394, 395]
private theorem transition1952Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1952Input0) = fromList transition1952Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1952 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0271 = 1 • support0061 := by
  have hs : support0271 = fromList transition1952Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1952Chunk0]
  have hn : (transition1952Raw0 : Multiset ℕ) = 1 • (supportNumbers0061 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0061] using hm

private def transition1953Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 264, 265, 266, 267, 392, 393, 394, 395, 512, 513, 514, 515, 640, 641, 642, 643, 776, 777, 778, 779, 904, 905, 906, 907]
private def transition1953Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 128, 672, 129, 673, 130, 674, 131, 675, 8, 552, 9, 553, 10, 554, 11, 555, 136, 680, 137, 681, 138, 682, 139, 683, 256, 800, 257, 801, 258, 802, 259, 803, 384, 928, 385, 929, 386, 930, 387, 931, 264, 808, 265, 809, 266, 810, 267, 811, 392, 936, 393, 937, 394, 938, 395, 939]
private theorem transition1953Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1953Input0) = fromList transition1953Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1953 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0271 = 1 • support0680 := by
  have hs : support0271 = fromList transition1953Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1953Chunk0]
  have hn : (transition1953Raw0 : Multiset ℕ) = 1 • (supportNumbers0680 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0680] using hm

private def transition1954Input0 : List ℕ := [0, 1, 2, 3, 512, 513, 514, 515]
private def transition1954Raw0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private theorem transition1954Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1954Input0) = fromList transition1954Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1954 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0272 = 1 • support0365 := by
  have hs : support0272 = fromList transition1954Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1954Chunk0]
  have hn : (transition1954Raw0 : Multiset ℕ) = 1 • (supportNumbers0365 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0365] using hm

private def transition1955Input0 : List ℕ := [0, 1, 2, 3, 512, 513, 514, 515]
private def transition1955Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 256, 896, 257, 897, 258, 898, 259, 899]
private theorem transition1955Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1955Input0) = fromList transition1955Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1955 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0272 = 1 • support0366 := by
  have hs : support0272 = fromList transition1955Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1955Chunk0]
  have hn : (transition1955Raw0 : Multiset ℕ) = 1 • (supportNumbers0366 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0366] using hm

private def transition1956Input0 : List ℕ := [0, 1, 2, 3, 512, 513, 514, 515]
private def transition1956Raw0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private theorem transition1956Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1956Input0) = fromList transition1956Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1956 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0272 = 1 • support0365 := by
  have hs : support0272 = fromList transition1956Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1956Chunk0]
  have hn : (transition1956Raw0 : Multiset ℕ) = 1 • (supportNumbers0365 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0365] using hm

private def transition1957Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition1957Raw0 : List ℕ := [0, 1, 2, 3]
private theorem transition1957Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1957Input0) = fromList transition1957Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1957 : nextSupport ⟨false, bits4 2⟩ ⟨false, bits4 4⟩ support0365 = 1 • support0030 := by
  have hs : support0365 = fromList transition1957Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1957Chunk0]
  have hn : (transition1957Raw0 : Multiset ℕ) = 1 • (supportNumbers0030 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0030] using hm

private def transition1958Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259]
private def transition1958Raw0 : List ℕ := [0, 1, 578, 579, 576, 577, 2, 3]
private theorem transition1958Chunk0 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1958Input0) = fromList transition1958Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1958 : nextSupport ⟨false, bits4 2⟩ ⟨true, bits4 4⟩ support0365 = 1 • support0681 := by
  have hs : support0365 = fromList transition1958Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1958Chunk0]
  have hn : (transition1958Raw0 : Multiset ℕ) = 1 • (supportNumbers0681 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0681] using hm

private def transition1959Input0 : List ℕ := [0, 1, 2, 3, 512, 513, 514, 515]
private def transition1959Raw0 : List ℕ := [0, 544, 1, 545, 2, 546, 3, 547, 256, 800, 257, 801, 258, 802, 259, 803]
private theorem transition1959Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1959Input0) = fromList transition1959Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1959 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 2⟩ support0272 = 1 • support1517 := by
  have hs : support0272 = fromList transition1959Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1959Chunk0]
  have hn : (transition1959Raw0 : Multiset ℕ) = 1 • (supportNumbers1517 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1517] using hm

private def transition1960Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 544, 545, 546, 547, 800, 801, 802, 803]
private def transition1960Raw0 : List ℕ := [0, 1, 2, 3, 0, 1, 2, 3, 288, 289, 290, 291, 288, 289, 290, 291]
private theorem transition1960Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ (fromList transition1960Input0) = fromList transition1960Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1960 : nextSupport ⟨true, bits4 2⟩ ⟨false, bits4 4⟩ support1517 = 2 • support0848 := by
  have hs : support1517 = fromList transition1960Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1960Chunk0]
  have hn : (transition1960Raw0 : Multiset ℕ) = 2 • (supportNumbers0848 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0848] using hm

private def transition1961Input0 : List ℕ := [0, 1, 2, 3, 256, 257, 258, 259, 544, 545, 546, 547, 800, 801, 802, 803]
private def transition1961Raw0 : List ℕ := [0, 576, 1, 577, 2, 578, 3, 579, 0, 576, 1, 577, 2, 578, 3, 579, 288, 864, 289, 865, 290, 866, 291, 867, 288, 864, 289, 865, 290, 866, 291, 867]
private theorem transition1961Chunk0 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ (fromList transition1961Input0) = fromList transition1961Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1961 : nextSupport ⟨true, bits4 2⟩ ⟨true, bits4 4⟩ support1517 = 2 • support0849 := by
  have hs : support1517 = fromList transition1961Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1961Chunk0]
  have hn : (transition1961Raw0 : Multiset ℕ) = 2 • (supportNumbers0849 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0849] using hm

private def transition1962Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1962Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1962Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1962Input0) = fromList transition1962Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1962 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 8⟩ support0273 = 1 • support0187 := by
  have hs : support0273 = fromList transition1962Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1962Chunk0]
  have hn : (transition1962Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1963Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1963Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 640, 641, 642, 643, 512, 513, 514, 515]
private theorem transition1963Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1963Input0) = fromList transition1963Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1963 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 8⟩ support0273 = 1 • support0364 := by
  have hs : support0273 = fromList transition1963Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1963Chunk0]
  have hn : (transition1963Raw0 : Multiset ℕ) = 1 • (supportNumbers0364 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0364] using hm

private def transition1964Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1964Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131]
private theorem transition1964Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1964Input0) = fromList transition1964Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1964 : nextSupport ⟨false, bits4 8⟩ ⟨false, bits4 2⟩ support0273 = 1 • support0187 := by
  have hs : support0273 = fromList transition1964Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1964Chunk0]
  have hn : (transition1964Raw0 : Multiset ℕ) = 1 • (supportNumbers0187 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0187] using hm

private def transition1965Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387]
private def transition1965Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 544, 545, 546, 547, 672, 673, 674, 675]
private theorem transition1965Chunk0 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ (fromList transition1965Input0) = fromList transition1965Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1965 : nextSupport ⟨false, bits4 8⟩ ⟨true, bits4 2⟩ support0273 = 1 • support1516 := by
  have hs : support0273 = fromList transition1965Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1965Chunk0]
  have hn : (transition1965Raw0 : Multiset ℕ) = 1 • (supportNumbers1516 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support1516] using hm

private def transition1966Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 512, 513, 514, 515, 640, 641, 642, 643, 768, 769, 770, 771, 896, 897, 898, 899]
private def transition1966Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 256, 257, 258, 259, 384, 385, 386, 387]
private theorem transition1966Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ (fromList transition1966Input0) = fromList transition1966Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1966 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 8⟩ support0274 = 2 • support0273 := by
  have hs : support0274 = fromList transition1966Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1966Chunk0]
  have hn : (transition1966Raw0 : Multiset ℕ) = 2 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm

private def transition1967Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 512, 513, 514, 515, 640, 641, 642, 643, 768, 769, 770, 771, 896, 897, 898, 899]
private def transition1967Raw0 : List ℕ := [0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 0, 640, 1, 641, 2, 642, 3, 643, 128, 512, 129, 513, 130, 514, 131, 515, 256, 896, 257, 897, 258, 898, 259, 899, 384, 768, 385, 769, 386, 770, 387, 771, 256, 896, 257, 897, 258, 898, 259, 899, 384, 768, 385, 769, 386, 770, 387, 771]
private theorem transition1967Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ (fromList transition1967Input0) = fromList transition1967Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1967 : nextSupport ⟨true, bits4 8⟩ ⟨true, bits4 8⟩ support0274 = 2 • support0274 := by
  have hs : support0274 = fromList transition1967Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1967Chunk0]
  have hn : (transition1967Raw0 : Multiset ℕ) = 2 • (supportNumbers0274 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0274] using hm

private def transition1968Input0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 512, 513, 514, 515, 640, 641, 642, 643, 768, 769, 770, 771, 896, 897, 898, 899]
private def transition1968Raw0 : List ℕ := [0, 1, 2, 3, 128, 129, 130, 131, 0, 1, 2, 3, 128, 129, 130, 131, 256, 257, 258, 259, 384, 385, 386, 387, 256, 257, 258, 259, 384, 385, 386, 387]
private theorem transition1968Chunk0 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ (fromList transition1968Input0) = fromList transition1968Raw0 := by
  rw [nextSupport_fromList]
  apply congrArg fromList
  decide +kernel

theorem transition1968 : nextSupport ⟨true, bits4 8⟩ ⟨false, bits4 2⟩ support0274 = 2 • support0273 := by
  have hs : support0274 = fromList transition1968Input0 := by rfl
  conv_lhs => rw [hs]
  simp only [nextSupport_add, transition1968Chunk0]
  have hn : (transition1968Raw0 : Multiset ℕ) = 2 • (supportNumbers0273 : Multiset ℕ) := by decide +kernel
  have hm := congrArg (Multiset.map point) hn
  simpa only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_coe, fromList, support0273] using hm


end UnifiedEJM.WeightedTransfer.SparseCertificate.Generated
