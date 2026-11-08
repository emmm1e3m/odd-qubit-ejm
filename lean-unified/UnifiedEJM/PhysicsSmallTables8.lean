import UnifiedEJM.PhysicsSmallBridge
open OddEJM Complex
open scoped BigOperators Matrix
namespace UnifiedEJM.PhysicsFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def smallDecode8 (k : Fin 256) : Bits 8 := ![((k.val / 128 : ℕ) : Bit), ((k.val / 64 : ℕ) : Bit), ((k.val / 32 : ℕ) : Bit), ((k.val / 16 : ℕ) : Bit), ((k.val / 8 : ℕ) : Bit), ((k.val / 4 : ℕ) : Bit), ((k.val / 2 : ℕ) : Bit), ((k.val / 1 : ℕ) : Bit)]

private theorem smallEncode8_bound (z : Bits 8) : 128 * (z 0).val + 64 * (z 1).val + 32 * (z 2).val + 16 * (z 3).val + 8 * (z 4).val + 4 * (z 5).val + 2 * (z 6).val + 1 * (z 7).val < 256 := by
  have h0 : (z 0).val < 2 := ZMod.val_lt _
  have h1 : (z 1).val < 2 := ZMod.val_lt _
  have h2 : (z 2).val < 2 := ZMod.val_lt _
  have h3 : (z 3).val < 2 := ZMod.val_lt _
  have h4 : (z 4).val < 2 := ZMod.val_lt _
  have h5 : (z 5).val < 2 := ZMod.val_lt _
  have h6 : (z 6).val < 2 := ZMod.val_lt _
  have h7 : (z 7).val < 2 := ZMod.val_lt _
  omega

def smallEncode8 (z : Bits 8) : Fin 256 := ⟨128 * (z 0).val + 64 * (z 1).val + 32 * (z 2).val + 16 * (z 3).val + 8 * (z 4).val + 4 * (z 5).val + 2 * (z 6).val + 1 * (z 7).val, smallEncode8_bound z⟩

def smallBlockIndex8 (b : Fin 4) (a : Fin 64) : Fin 256 :=
  ⟨b.val * 64 + a.val, by have hb := b.isLt; have ha := a.isLt; omega⟩

theorem smallBlock_surjective8 (k : Fin 256) :
    ∃ b a, smallBlockIndex8 b a = k := by
  refine ⟨⟨k.val / 64, by have hk := k.isLt; omega⟩,
    ⟨k.val % 64, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  dsimp [smallBlockIndex8]
  omega

private theorem small_encode_decode8_block0 : ∀ a : Fin 64, smallEncode8 (smallDecode8 (smallBlockIndex8 0 a)) = (smallBlockIndex8 0 a) := by
  decide +kernel

private theorem small_encode_decode8_block1 : ∀ a : Fin 64, smallEncode8 (smallDecode8 (smallBlockIndex8 1 a)) = (smallBlockIndex8 1 a) := by
  decide +kernel

private theorem small_encode_decode8_block2 : ∀ a : Fin 64, smallEncode8 (smallDecode8 (smallBlockIndex8 2 a)) = (smallBlockIndex8 2 a) := by
  decide +kernel

private theorem small_encode_decode8_block3 : ∀ a : Fin 64, smallEncode8 (smallDecode8 (smallBlockIndex8 3 a)) = (smallBlockIndex8 3 a) := by
  decide +kernel

theorem small_encode_decode8 : ∀ k : Fin 256, smallEncode8 (smallDecode8 k) = k := by
  intro k
  obtain ⟨b, a, rfl⟩ := smallBlock_surjective8 k
  fin_cases b
  · exact small_encode_decode8_block0 a
  · exact small_encode_decode8_block1 a
  · exact small_encode_decode8_block2 a
  · exact small_encode_decode8_block3 a

theorem small_decode_encode8 : ∀ z : Bits 8, smallDecode8 (smallEncode8 z) = z := by
  have hb : Function.Bijective smallDecode8 :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Function.LeftInverse.injective small_encode_decode8, by simp [Bits, Bit]⟩
  intro z
  obtain ⟨k, rfl⟩ := hb.2 z
  rw [small_encode_decode8]

def smallIndexEquiv8 : Fin 256 ≃ Bits 8 where
  toFun := smallDecode8
  invFun := smallEncode8
  left_inv := small_encode_decode8
  right_inv := small_decode_encode8

def small8A (k : Fin 256) : G := (if k.val < 128 then (if k.val < 64 then (if k.val < 32 then (if k.val < 16 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then (if k.val < 1 then ⟨2, 0⟩ else ⟨1, -1⟩) else (if k.val < 3 then ⟨0, 0⟩ else ⟨1, 0⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 7 then ⟨0, 0⟩ else ⟨0, -1⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 11 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨-1, 0⟩ else ⟨-1, 1⟩) else (if k.val < 15 then ⟨0, 0⟩ else ⟨1, 0⟩)))) else (if k.val < 24 then (if k.val < 20 then (if k.val < 18 then (if k.val < 17 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 19 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 22 then (if k.val < 21 then ⟨1, 0⟩ else ⟨1, -1⟩) else (if k.val < 23 then ⟨0, 0⟩ else ⟨-1, 0⟩))) else (if k.val < 28 then (if k.val < 26 then (if k.val < 25 then ⟨-1, 0⟩ else ⟨-1, 1⟩) else (if k.val < 27 then ⟨0, 0⟩ else ⟨-1, 0⟩)) else (if k.val < 30 then (if k.val < 29 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 31 then ⟨0, 0⟩ else ⟨0, -1⟩))))) else (if k.val < 48 then (if k.val < 40 then (if k.val < 36 then (if k.val < 34 then (if k.val < 33 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 35 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 38 then (if k.val < 37 then ⟨1, 0⟩ else ⟨1, -1⟩) else (if k.val < 39 then ⟨0, 0⟩ else ⟨-1, 0⟩))) else (if k.val < 44 then (if k.val < 42 then (if k.val < 41 then ⟨1, 0⟩ else ⟨1, -1⟩) else (if k.val < 43 then ⟨0, 0⟩ else ⟨1, 0⟩)) else (if k.val < 46 then (if k.val < 45 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 47 then ⟨0, 0⟩ else ⟨0, 1⟩)))) else (if k.val < 56 then (if k.val < 52 then (if k.val < 50 then (if k.val < 49 then ⟨-1, 0⟩ else ⟨-1, 1⟩) else (if k.val < 51 then ⟨0, 0⟩ else ⟨-1, 0⟩)) else (if k.val < 54 then (if k.val < 53 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 55 then ⟨0, 0⟩ else ⟨0, 1⟩))) else (if k.val < 60 then (if k.val < 58 then (if k.val < 57 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 59 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 62 then (if k.val < 61 then ⟨-1, 0⟩ else ⟨-1, 1⟩) else (if k.val < 63 then ⟨0, 0⟩ else ⟨1, 0⟩)))))) else (if k.val < 96 then (if k.val < 80 then (if k.val < 72 then (if k.val < 68 then (if k.val < 66 then (if k.val < 65 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 67 then ⟨0, -1⟩ else ⟨-1, 1⟩)) else (if k.val < 70 then (if k.val < 69 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 71 then ⟨0, 0⟩ else ⟨-1, 0⟩))) else (if k.val < 76 then (if k.val < 74 then (if k.val < 73 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 75 then ⟨0, 0⟩ else ⟨1, 0⟩)) else (if k.val < 78 then (if k.val < 77 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 79 then ⟨0, -1⟩ else ⟨-1, 1⟩)))) else (if k.val < 88 then (if k.val < 84 then (if k.val < 82 then (if k.val < 81 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 83 then ⟨0, 0⟩ else ⟨1, 0⟩)) else (if k.val < 86 then (if k.val < 85 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 87 then ⟨0, 1⟩ else ⟨1, -1⟩))) else (if k.val < 92 then (if k.val < 90 then (if k.val < 89 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 91 then ⟨0, 1⟩ else ⟨1, -1⟩)) else (if k.val < 94 then (if k.val < 93 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 95 then ⟨0, 0⟩ else ⟨-1, 0⟩))))) else (if k.val < 112 then (if k.val < 104 then (if k.val < 100 then (if k.val < 98 then (if k.val < 97 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 99 then ⟨0, 0⟩ else ⟨-1, 0⟩)) else (if k.val < 102 then (if k.val < 101 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 103 then ⟨0, -1⟩ else ⟨-1, 1⟩))) else (if k.val < 108 then (if k.val < 106 then (if k.val < 105 then ⟨0, 0⟩ else ⟨0, -1⟩) else (if k.val < 107 then ⟨0, 1⟩ else ⟨1, -1⟩)) else (if k.val < 110 then (if k.val < 109 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 111 then ⟨0, 0⟩ else ⟨-1, 0⟩)))) else (if k.val < 120 then (if k.val < 116 then (if k.val < 114 then (if k.val < 113 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 115 then ⟨0, -1⟩ else ⟨-1, 1⟩)) else (if k.val < 118 then (if k.val < 117 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 119 then ⟨0, 0⟩ else ⟨-1, 0⟩))) else (if k.val < 124 then (if k.val < 122 then (if k.val < 121 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 123 then ⟨0, 0⟩ else ⟨-1, 0⟩)) else (if k.val < 126 then (if k.val < 125 then ⟨0, 0⟩ else ⟨0, 1⟩) else (if k.val < 127 then ⟨0, 1⟩ else ⟨1, -1⟩))))))) else (if k.val < 192 then (if k.val < 160 then (if k.val < 144 then (if k.val < 136 then (if k.val < 132 then (if k.val < 130 then (if k.val < 129 then ⟨1, 1⟩ else ⟨0, 1⟩) else (if k.val < 131 then ⟨0, -1⟩ else ⟨0, 0⟩)) else (if k.val < 134 then (if k.val < 133 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 135 then ⟨-1, 0⟩ else ⟨0, 0⟩))) else (if k.val < 140 then (if k.val < 138 then (if k.val < 137 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 139 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 142 then (if k.val < 141 then ⟨-1, -1⟩ else ⟨0, -1⟩) else (if k.val < 143 then ⟨0, -1⟩ else ⟨0, 0⟩)))) else (if k.val < 152 then (if k.val < 148 then (if k.val < 146 then (if k.val < 145 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 147 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 150 then (if k.val < 149 then ⟨1, 1⟩ else ⟨0, 1⟩) else (if k.val < 151 then ⟨0, 1⟩ else ⟨0, 0⟩))) else (if k.val < 156 then (if k.val < 154 then (if k.val < 153 then ⟨-1, -1⟩ else ⟨0, -1⟩) else (if k.val < 155 then ⟨0, 1⟩ else ⟨0, 0⟩)) else (if k.val < 158 then (if k.val < 157 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 159 then ⟨-1, 0⟩ else ⟨0, 0⟩))))) else (if k.val < 176 then (if k.val < 168 then (if k.val < 164 then (if k.val < 162 then (if k.val < 161 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 163 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 166 then (if k.val < 165 then ⟨1, 1⟩ else ⟨0, 1⟩) else (if k.val < 167 then ⟨0, 1⟩ else ⟨0, 0⟩))) else (if k.val < 172 then (if k.val < 170 then (if k.val < 169 then ⟨1, 1⟩ else ⟨0, 1⟩) else (if k.val < 171 then ⟨0, -1⟩ else ⟨0, 0⟩)) else (if k.val < 174 then (if k.val < 173 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 175 then ⟨1, 0⟩ else ⟨0, 0⟩)))) else (if k.val < 184 then (if k.val < 180 then (if k.val < 178 then (if k.val < 177 then ⟨-1, -1⟩ else ⟨0, -1⟩) else (if k.val < 179 then ⟨0, 1⟩ else ⟨0, 0⟩)) else (if k.val < 182 then (if k.val < 181 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 183 then ⟨1, 0⟩ else ⟨0, 0⟩))) else (if k.val < 188 then (if k.val < 186 then (if k.val < 185 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 187 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 190 then (if k.val < 189 then ⟨-1, -1⟩ else ⟨0, -1⟩) else (if k.val < 191 then ⟨0, -1⟩ else ⟨0, 0⟩)))))) else (if k.val < 224 then (if k.val < 208 then (if k.val < 200 then (if k.val < 196 then (if k.val < 194 then (if k.val < 193 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 195 then ⟨-1, -1⟩ else ⟨1, 0⟩)) else (if k.val < 198 then (if k.val < 197 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 199 then ⟨0, -1⟩ else ⟨0, 0⟩))) else (if k.val < 204 then (if k.val < 202 then (if k.val < 201 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 203 then ⟨0, 1⟩ else ⟨0, 0⟩)) else (if k.val < 206 then (if k.val < 205 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 207 then ⟨-1, -1⟩ else ⟨1, 0⟩)))) else (if k.val < 216 then (if k.val < 212 then (if k.val < 210 then (if k.val < 209 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 211 then ⟨0, 1⟩ else ⟨0, 0⟩)) else (if k.val < 214 then (if k.val < 213 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 215 then ⟨1, 1⟩ else ⟨-1, 0⟩))) else (if k.val < 220 then (if k.val < 218 then (if k.val < 217 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 219 then ⟨1, 1⟩ else ⟨-1, 0⟩)) else (if k.val < 222 then (if k.val < 221 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 223 then ⟨0, -1⟩ else ⟨0, 0⟩))))) else (if k.val < 240 then (if k.val < 232 then (if k.val < 228 then (if k.val < 226 then (if k.val < 225 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 227 then ⟨0, -1⟩ else ⟨0, 0⟩)) else (if k.val < 230 then (if k.val < 229 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 231 then ⟨-1, -1⟩ else ⟨1, 0⟩))) else (if k.val < 236 then (if k.val < 234 then (if k.val < 233 then ⟨-1, 0⟩ else ⟨0, 0⟩) else (if k.val < 235 then ⟨1, 1⟩ else ⟨-1, 0⟩)) else (if k.val < 238 then (if k.val < 237 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 239 then ⟨0, -1⟩ else ⟨0, 0⟩)))) else (if k.val < 248 then (if k.val < 244 then (if k.val < 242 then (if k.val < 241 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 243 then ⟨-1, -1⟩ else ⟨1, 0⟩)) else (if k.val < 246 then (if k.val < 245 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 247 then ⟨0, -1⟩ else ⟨0, 0⟩))) else (if k.val < 252 then (if k.val < 250 then (if k.val < 249 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 251 then ⟨0, -1⟩ else ⟨0, 0⟩)) else (if k.val < 254 then (if k.val < 253 then ⟨1, 0⟩ else ⟨0, 0⟩) else (if k.val < 255 then ⟨1, 1⟩ else ⟨0, 0⟩))))))))

private theorem small8A_checked_block0 : ∀ a : Fin 64, coeffA UnifiedEJM.q (smallDecode8 (smallBlockIndex8 0 a)) = small8A (smallBlockIndex8 0 a) := by
  decide +kernel

private theorem small8A_checked_block1 : ∀ a : Fin 64, coeffA UnifiedEJM.q (smallDecode8 (smallBlockIndex8 1 a)) = small8A (smallBlockIndex8 1 a) := by
  decide +kernel

private theorem small8A_checked_block2 : ∀ a : Fin 64, coeffA UnifiedEJM.q (smallDecode8 (smallBlockIndex8 2 a)) = small8A (smallBlockIndex8 2 a) := by
  decide +kernel

private theorem small8A_checked_block3 : ∀ a : Fin 64, coeffA UnifiedEJM.q (smallDecode8 (smallBlockIndex8 3 a)) = small8A (smallBlockIndex8 3 a) := by
  decide +kernel

theorem small8A_checked : ∀ k : Fin 256, coeffA UnifiedEJM.q (smallDecode8 k) = small8A k := by
  intro k
  obtain ⟨b, a, rfl⟩ := smallBlock_surjective8 k
  fin_cases b
  · exact small8A_checked_block0 a
  · exact small8A_checked_block1 a
  · exact small8A_checked_block2 a
  · exact small8A_checked_block3 a

def small8B (k : Fin 256) : G := (if k.val < 128 then (if k.val < 64 then (if k.val < 32 then (if k.val < 16 then (if k.val < 8 then (if k.val < 4 then (if k.val < 2 then ⟨0, 0⟩ else (if k.val < 3 then ⟨-1, 1⟩ else ⟨0, -1⟩)) else (if k.val < 6 then (if k.val < 5 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 7 then ⟨-1, 1⟩ else ⟨1, 0⟩))) else (if k.val < 12 then (if k.val < 10 then (if k.val < 9 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 11 then ⟨1, -1⟩ else ⟨-1, 0⟩)) else (if k.val < 14 then (if k.val < 13 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 15 then ⟨-1, 1⟩ else ⟨0, -1⟩)))) else (if k.val < 24 then (if k.val < 20 then (if k.val < 18 then (if k.val < 17 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 19 then ⟨1, -1⟩ else ⟨-1, 0⟩)) else (if k.val < 22 then (if k.val < 21 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 23 then ⟨1, -1⟩ else ⟨0, 1⟩))) else (if k.val < 28 then (if k.val < 26 then (if k.val < 25 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 27 then ⟨1, -1⟩ else ⟨0, 1⟩)) else (if k.val < 30 then (if k.val < 29 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 31 then ⟨-1, 1⟩ else ⟨1, 0⟩))))) else (if k.val < 48 then (if k.val < 40 then (if k.val < 36 then (if k.val < 34 then (if k.val < 33 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 35 then ⟨1, -1⟩ else ⟨-1, 0⟩)) else (if k.val < 38 then (if k.val < 37 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 39 then ⟨1, -1⟩ else ⟨0, 1⟩))) else (if k.val < 44 then (if k.val < 42 then (if k.val < 41 then ⟨0, -1⟩ else ⟨0, 0⟩) else (if k.val < 43 then ⟨-1, 1⟩ else ⟨0, -1⟩)) else (if k.val < 46 then (if k.val < 45 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 47 then ⟨1, -1⟩ else ⟨-1, 0⟩)))) else (if k.val < 56 then (if k.val < 52 then (if k.val < 50 then (if k.val < 49 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 51 then ⟨1, -1⟩ else ⟨0, 1⟩)) else (if k.val < 54 then (if k.val < 53 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 55 then ⟨1, -1⟩ else ⟨-1, 0⟩))) else (if k.val < 60 then (if k.val < 58 then (if k.val < 57 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 59 then ⟨1, -1⟩ else ⟨-1, 0⟩)) else (if k.val < 62 then (if k.val < 61 then ⟨0, 1⟩ else ⟨0, 0⟩) else (if k.val < 63 then ⟨-1, 1⟩ else ⟨0, -1⟩)))))) else (if k.val < 96 then (if k.val < 80 then (if k.val < 72 then (if k.val < 68 then (if k.val < 66 then (if k.val < 65 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 67 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 70 then (if k.val < 69 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 71 then ⟨1, -1⟩ else ⟨0, 1⟩))) else (if k.val < 76 then (if k.val < 74 then (if k.val < 73 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 75 then ⟨-1, 1⟩ else ⟨0, -1⟩)) else (if k.val < 78 then (if k.val < 77 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 79 then ⟨1, 0⟩ else ⟨0, 0⟩)))) else (if k.val < 88 then (if k.val < 84 then (if k.val < 82 then (if k.val < 81 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 83 then ⟨-1, 1⟩ else ⟨0, -1⟩)) else (if k.val < 86 then (if k.val < 85 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 87 then ⟨-1, 0⟩ else ⟨0, 0⟩))) else (if k.val < 92 then (if k.val < 90 then (if k.val < 89 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 91 then ⟨-1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 94 then (if k.val < 93 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 95 then ⟨1, -1⟩ else ⟨0, 1⟩))))) else (if k.val < 112 then (if k.val < 104 then (if k.val < 100 then (if k.val < 98 then (if k.val < 97 then ⟨-1, 1⟩ else ⟨0, 1⟩) else (if k.val < 99 then ⟨1, -1⟩ else ⟨0, 1⟩)) else (if k.val < 102 then (if k.val < 101 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 103 then ⟨1, 0⟩ else ⟨0, 0⟩))) else (if k.val < 108 then (if k.val < 106 then (if k.val < 105 then ⟨1, -1⟩ else ⟨1, 0⟩) else (if k.val < 107 then ⟨-1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 110 then (if k.val < 109 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 111 then ⟨1, -1⟩ else ⟨0, 1⟩)))) else (if k.val < 120 then (if k.val < 116 then (if k.val < 114 then (if k.val < 113 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 115 then ⟨1, 0⟩ else ⟨0, 0⟩)) else (if k.val < 118 then (if k.val < 117 then ⟨1, -1⟩ else ⟨0, -1⟩) else (if k.val < 119 then ⟨1, -1⟩ else ⟨0, 1⟩))) else (if k.val < 124 then (if k.val < 122 then (if k.val < 121 then ⟨-1, 1⟩ else ⟨0, 1⟩) else (if k.val < 123 then ⟨1, -1⟩ else ⟨0, 1⟩)) else (if k.val < 126 then (if k.val < 125 then ⟨-1, 1⟩ else ⟨-1, 0⟩) else (if k.val < 127 then ⟨-1, 0⟩ else ⟨0, 0⟩))))))) else (if k.val < 192 then (if k.val < 160 then (if k.val < 144 then (if k.val < 136 then (if k.val < 132 then (if k.val < 130 then (if k.val < 129 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 131 then ⟨-1, 0⟩ else ⟨1, 1⟩)) else (if k.val < 134 then (if k.val < 133 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 135 then ⟨0, -1⟩ else ⟨1, 1⟩))) else (if k.val < 140 then (if k.val < 138 then (if k.val < 137 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 139 then ⟨0, 1⟩ else ⟨-1, -1⟩)) else (if k.val < 142 then (if k.val < 141 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 143 then ⟨-1, 0⟩ else ⟨1, 1⟩)))) else (if k.val < 152 then (if k.val < 148 then (if k.val < 146 then (if k.val < 145 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 147 then ⟨0, 1⟩ else ⟨-1, -1⟩)) else (if k.val < 150 then (if k.val < 149 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 151 then ⟨1, 0⟩ else ⟨-1, -1⟩))) else (if k.val < 156 then (if k.val < 154 then (if k.val < 153 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 155 then ⟨1, 0⟩ else ⟨-1, -1⟩)) else (if k.val < 158 then (if k.val < 157 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 159 then ⟨0, -1⟩ else ⟨1, 1⟩))))) else (if k.val < 176 then (if k.val < 168 then (if k.val < 164 then (if k.val < 162 then (if k.val < 161 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 163 then ⟨0, 1⟩ else ⟨-1, -1⟩)) else (if k.val < 166 then (if k.val < 165 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 167 then ⟨1, 0⟩ else ⟨-1, -1⟩))) else (if k.val < 172 then (if k.val < 170 then (if k.val < 169 then ⟨0, 0⟩ else ⟨1, 0⟩) else (if k.val < 171 then ⟨-1, 0⟩ else ⟨1, 1⟩)) else (if k.val < 174 then (if k.val < 173 then ⟨0, 1⟩ else ⟨1, 1⟩) else (if k.val < 175 then ⟨0, 1⟩ else ⟨-1, -1⟩)))) else (if k.val < 184 then (if k.val < 180 then (if k.val < 178 then (if k.val < 177 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 179 then ⟨1, 0⟩ else ⟨-1, -1⟩)) else (if k.val < 182 then (if k.val < 181 then ⟨0, 1⟩ else ⟨1, 1⟩) else (if k.val < 183 then ⟨0, 1⟩ else ⟨-1, -1⟩))) else (if k.val < 188 then (if k.val < 186 then (if k.val < 185 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 187 then ⟨0, 1⟩ else ⟨-1, -1⟩)) else (if k.val < 190 then (if k.val < 189 then ⟨0, 0⟩ else ⟨-1, 0⟩) else (if k.val < 191 then ⟨-1, 0⟩ else ⟨1, 1⟩)))))) else (if k.val < 224 then (if k.val < 208 then (if k.val < 200 then (if k.val < 196 then (if k.val < 194 then (if k.val < 193 then ⟨0, 1⟩ else ⟨1, 1⟩) else (if k.val < 195 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 198 then (if k.val < 197 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 199 then ⟨-1, 0⟩ else ⟨1, 1⟩))) else (if k.val < 204 then (if k.val < 202 then (if k.val < 201 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 203 then ⟨1, 0⟩ else ⟨-1, -1⟩)) else (if k.val < 206 then (if k.val < 205 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 207 then ⟨0, 0⟩ else ⟨0, 1⟩)))) else (if k.val < 216 then (if k.val < 212 then (if k.val < 210 then (if k.val < 209 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 211 then ⟨1, 0⟩ else ⟨-1, -1⟩)) else (if k.val < 214 then (if k.val < 213 then ⟨0, 1⟩ else ⟨1, 1⟩) else (if k.val < 215 then ⟨0, 0⟩ else ⟨0, -1⟩))) else (if k.val < 220 then (if k.val < 218 then (if k.val < 217 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 219 then ⟨0, 0⟩ else ⟨0, -1⟩)) else (if k.val < 222 then (if k.val < 221 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 223 then ⟨-1, 0⟩ else ⟨1, 1⟩))))) else (if k.val < 240 then (if k.val < 232 then (if k.val < 228 then (if k.val < 226 then (if k.val < 225 then ⟨1, 0⟩ else ⟨1, 1⟩) else (if k.val < 227 then ⟨-1, 0⟩ else ⟨1, 1⟩)) else (if k.val < 230 then (if k.val < 229 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 231 then ⟨0, 0⟩ else ⟨0, 1⟩))) else (if k.val < 236 then (if k.val < 234 then (if k.val < 233 then ⟨0, -1⟩ else ⟨-1, -1⟩) else (if k.val < 235 then ⟨0, 0⟩ else ⟨0, -1⟩)) else (if k.val < 238 then (if k.val < 237 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 239 then ⟨-1, 0⟩ else ⟨1, 1⟩)))) else (if k.val < 248 then (if k.val < 244 then (if k.val < 242 then (if k.val < 241 then ⟨0, 1⟩ else ⟨1, 1⟩) else (if k.val < 243 then ⟨0, 0⟩ else ⟨0, 1⟩)) else (if k.val < 246 then (if k.val < 245 then ⟨-1, 0⟩ else ⟨-1, -1⟩) else (if k.val < 247 then ⟨-1, 0⟩ else ⟨1, 1⟩))) else (if k.val < 252 then (if k.val < 250 then (if k.val < 249 then ⟨1, 0⟩ else ⟨1, 1⟩) else (if k.val < 251 then ⟨-1, 0⟩ else ⟨1, 1⟩)) else (if k.val < 254 then (if k.val < 253 then ⟨0, 1⟩ else ⟨1, 1⟩) else ⟨0, 0⟩)))))))

private theorem small8B_checked_block0 : ∀ a : Fin 64, coeffB UnifiedEJM.q (smallDecode8 (smallBlockIndex8 0 a)) = small8B (smallBlockIndex8 0 a) := by
  decide +kernel

private theorem small8B_checked_block1 : ∀ a : Fin 64, coeffB UnifiedEJM.q (smallDecode8 (smallBlockIndex8 1 a)) = small8B (smallBlockIndex8 1 a) := by
  decide +kernel

private theorem small8B_checked_block2 : ∀ a : Fin 64, coeffB UnifiedEJM.q (smallDecode8 (smallBlockIndex8 2 a)) = small8B (smallBlockIndex8 2 a) := by
  decide +kernel

private theorem small8B_checked_block3 : ∀ a : Fin 64, coeffB UnifiedEJM.q (smallDecode8 (smallBlockIndex8 3 a)) = small8B (smallBlockIndex8 3 a) := by
  decide +kernel

theorem small8B_checked : ∀ k : Fin 256, coeffB UnifiedEJM.q (smallDecode8 k) = small8B k := by
  intro k
  obtain ⟨b, a, rfl⟩ := smallBlock_surjective8 k
  fin_cases b
  · exact small8B_checked_block0 a
  · exact small8B_checked_block1 a
  · exact small8B_checked_block2 a
  · exact small8B_checked_block3 a

end UnifiedEJM.PhysicsFinite
