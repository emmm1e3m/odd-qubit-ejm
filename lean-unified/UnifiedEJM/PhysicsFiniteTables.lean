import UnifiedEJM.PhysicsFinite

open OddEJM Complex
open scoped BigOperators
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def decode5 (k : Fin 32) : Bits 5 := ![((k.val / 16 : ℕ) : Bit), ((k.val / 8 : ℕ) : Bit), ((k.val / 4 : ℕ) : Bit), ((k.val / 2 : ℕ) : Bit), ((k.val / 1 : ℕ) : Bit)]
private theorem encode5_bound : ∀ z : Bits 5, 16 * (z 0).val + 8 * (z 1).val + 4 * (z 2).val + 2 * (z 3).val + 1 * (z 4).val < 32 := by decide +kernel
def encode5 (z : Bits 5) : Fin 32 := ⟨16 * (z 0).val + 8 * (z 1).val + 4 * (z 2).val + 2 * (z 3).val + 1 * (z 4).val, encode5_bound z⟩
theorem encode_decode5 : ∀ k : Fin 32, encode5 (decode5 k) = k := by decide +kernel
theorem decode_encode5 : ∀ z : Bits 5, decode5 (encode5 z) = z := by decide +kernel
def indexEquiv5 : Fin 32 ≃ Bits 5 where
  toFun := decode5
  invFun := encode5
  left_inv := encode_decode5
  right_inv := decode_encode5

def new5A : Fin 32 → G := ![⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]
def new5B : Fin 32 → G := ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]
theorem new5A_checked : ∀ k : Fin 32, coeffA UnifiedEJM.q (decode5 k) = new5A k := by decide +kernel
theorem new5B_checked : ∀ k : Fin 32, coeffB UnifiedEJM.q (decode5 k) = new5B k := by decide +kernel

def decode6 (k : Fin 64) : Bits 6 := ![((k.val / 32 : ℕ) : Bit), ((k.val / 16 : ℕ) : Bit), ((k.val / 8 : ℕ) : Bit), ((k.val / 4 : ℕ) : Bit), ((k.val / 2 : ℕ) : Bit), ((k.val / 1 : ℕ) : Bit)]
private theorem encode6_bound : ∀ z : Bits 6, 32 * (z 0).val + 16 * (z 1).val + 8 * (z 2).val + 4 * (z 3).val + 2 * (z 4).val + 1 * (z 5).val < 64 := by decide +kernel
def encode6 (z : Bits 6) : Fin 64 := ⟨32 * (z 0).val + 16 * (z 1).val + 8 * (z 2).val + 4 * (z 3).val + 2 * (z 4).val + 1 * (z 5).val, encode6_bound z⟩
theorem encode_decode6 : ∀ k : Fin 64, encode6 (decode6 k) = k := by decide +kernel
theorem decode_encode6 : ∀ z : Bits 6, decode6 (encode6 z) = z := by decide +kernel
def indexEquiv6 : Fin 64 ≃ Bits 6 where
  toFun := decode6
  invFun := encode6
  left_inv := encode_decode6
  right_inv := decode_encode6

def new6A : Fin 64 → G := ![⟨2, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]
def new6B : Fin 64 → G := ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]
theorem new6A_checked : ∀ k : Fin 64, coeffA UnifiedEJM.q (decode6 k) = new6A k := by decide +kernel
theorem new6B_checked : ∀ k : Fin 64, coeffB UnifiedEJM.q (decode6 k) = new6B k := by decide +kernel

def pg6A : Fin 64 → G := ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩]
def pg6B : Fin 64 → G := ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩]
theorem pg6A_checked : ∀ k : Fin 64, coeffA UnifiedEJM.EvenWalsh.qA (decode6 k) = pg6A k := by decide +kernel
theorem pg6B_checked : ∀ k : Fin 64, coeffB UnifiedEJM.EvenWalsh.qA (decode6 k) = pg6B k := by decide +kernel

end UnifiedEJM.PhysicsFinite
