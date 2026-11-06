import UnifiedEJM.PhysicsPGIndexed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

noncomputable section
open scoped BigOperators Matrix
open OddEJM Complex

namespace UnifiedEJM.PhysicsSpectra
open UnifiedEJM.PhysicsFinite UnifiedEJM.Multipartite

set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev firstTwo5 : Finset (Fin 5) := {0,1}
abbrev firstTwo6 : Finset (Fin 6) := {0,1}

def join5 (i : Fin 4) (k : Fin 8) : Fin 32 := ⟨8*i.val+k.val, by omega⟩
def join6 (i : Fin 4) (k : Fin 16) : Fin 64 := ⟨16*i.val+k.val, by omega⟩

def pair5 (i : Fin 4) : Side firstTwo5 := fun j => PhysicsFinite.decode5 (join5 i 0) j
def tail5 (k : Fin 8) : OtherSide firstTwo5 := fun j => PhysicsFinite.decode5 (join5 0 k) j
def pair6 (i : Fin 4) : Side firstTwo6 := fun j => decode6 (join6 i 0) j
def tail6 (k : Fin 16) : OtherSide firstTwo6 := fun j => decode6 (join6 0 k) j

theorem pair5_bijective : Function.Bijective pair5 := by decide +kernel
theorem tail5_bijective : Function.Bijective tail5 := by decide +kernel
theorem pair6_bijective : Function.Bijective pair6 := by decide +kernel
theorem tail6_bijective : Function.Bijective tail6 := by decide +kernel

def pairEquiv5 : Fin 4 ≃ Side firstTwo5 := Equiv.ofBijective pair5 pair5_bijective
def tailEquiv5 : Fin 8 ≃ OtherSide firstTwo5 := Equiv.ofBijective tail5 tail5_bijective
def pairEquiv6 : Fin 4 ≃ Side firstTwo6 := Equiv.ofBijective pair6 pair6_bijective
def tailEquiv6 : Fin 16 ≃ OtherSide firstTwo6 := Equiv.ofBijective tail6 tail6_bijective

theorem merge5_checked : ∀ (i : Fin 4) (k : Fin 8),
    (split firstTwo5).symm (pair5 i, tail5 k) = PhysicsFinite.decode5 (join5 i k) := by decide +kernel
theorem merge6_checked : ∀ (i : Fin 4) (k : Fin 16),
    (split firstTwo6).symm (pair6 i, tail6 k) = decode6 (join6 i k) := by decide +kernel

/-- 原偏迹在00,01,10,11排列下的逐项重索引；未预设谱。 -/
theorem reduced5_index (ψ : Vec 5) (i j : Fin 4) :
    reduced firstTwo5 ψ (pairEquiv5 i) (pairEquiv5 j) =
      ∑ k : Fin 8, ψ (PhysicsFinite.decode5 (join5 i k)) * star (ψ (PhysicsFinite.decode5 (join5 j k))) := by
  rw [reduced_apply, ← tailEquiv5.sum_comp]
  change (∑ k : Fin 8, ψ ((split firstTwo5).symm (pair5 i,tail5 k)) *
    star (ψ ((split firstTwo5).symm (pair5 j,tail5 k)))) = _
  simp_rw [merge5_checked]

theorem reduced6_index (ψ : Vec 6) (i j : Fin 4) :
    reduced firstTwo6 ψ (pairEquiv6 i) (pairEquiv6 j) =
      ∑ k : Fin 16, ψ (decode6 (join6 i k)) * star (ψ (decode6 (join6 j k))) := by
  rw [reduced_apply, ← tailEquiv6.sum_comp]
  change (∑ k : Fin 16, ψ ((split firstTwo6).symm (pair6 i,tail6 k)) *
    star (ψ ((split firstTwo6).symm (pair6 j,tail6 k)))) = _
  simp_rw [merge6_checked]

def numerator5 (k : Fin 32) : G := new5A k + gi * new5B k
def numerator6 (k : Fin 64) : G := new6A k + gi * new6B k

def gram5 (i j : Fin 4) : G :=
  ∑ k : Fin 8, numerator5 (join5 i k) * star (numerator5 (join5 j k))
def gram6 (i j : Fin 4) : G :=
  ∑ k : Fin 16, numerator6 (join6 i k) * star (numerator6 (join6 j k))

def gramTable5 : Matrix (Fin 4) (Fin 4) G :=
  !![⟨16,0⟩,⟨0,4⟩,⟨0,-8⟩,⟨-4,0⟩;
     ⟨0,-4⟩,⟨16,0⟩,⟨-4,0⟩,⟨0,8⟩;
     ⟨0,8⟩,⟨-4,0⟩,⟨16,0⟩,⟨0,-4⟩;
     ⟨-4,0⟩,⟨0,-8⟩,⟨0,4⟩,⟨16,0⟩]

def gramTable6 : Matrix (Fin 4) (Fin 4) G :=
  !![⟨32,0⟩,0,⟨0,-16⟩,0;
     0,⟨32,0⟩,0,⟨0,16⟩;
     ⟨0,16⟩,0,⟨32,0⟩,0;
     0,⟨0,-16⟩,0,⟨32,0⟩]

theorem gram5_checked : ∀ i j, gram5 i j = gramTable5 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel
theorem gram6_checked : ∀ i j, gram6 i j = gramTable6 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem reduced5_gram (i j : Fin 4) :
    reduced firstTwo5 (Physical.seed (UnifiedEJM.rawPhase I)) (pairEquiv5 i) (pairEquiv5 j) =
      (1/64 : ℂ) * (gramTable5 i j : ℂ) := by
  rw [reduced5_index]
  simp_rw [seed5_index]
  have hi (k : Fin 32) : (new5A k : ℂ) + I * (new5B k : ℂ) = (numerator5 k : ℂ) := by
    simp [numerator5, map_add, map_mul]
  simp_rw [hi, star_mul]
  calc
    _ = (scale 5 * star (scale 5)) * (gram5 i j : ℂ) := by
      simp only [gram5, map_sum, map_mul, GaussianInt.toComplex_star, Complex.star_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [scale_norm, gram5_checked]; norm_num

theorem reduced6_gram (i j : Fin 4) :
    reduced firstTwo6 (Physical.seed (UnifiedEJM.rawPhase I)) (pairEquiv6 i) (pairEquiv6 j) =
      (1/128 : ℂ) * (gramTable6 i j : ℂ) := by
  rw [reduced6_index]
  simp_rw [seed6_index]
  have hi (k : Fin 64) : (new6A k : ℂ) + I * (new6B k : ℂ) = (numerator6 k : ℂ) := by
    simp [numerator6, map_add, map_mul]
  simp_rw [hi, star_mul]
  calc
    _ = (scale 6 * star (scale 6)) * (gram6 i j : ℂ) := by
      simp only [gram6, map_sum, map_mul, GaussianInt.toComplex_star, Complex.star_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [scale_norm, gram6_checked]; norm_num

def numeratorPG6 (k : Fin 64) : G := pg6A k + gi * pg6B k
def gramPG6 (i j : Fin 4) : G :=
  ∑ k : Fin 16, numeratorPG6 (join6 i k) * star (numeratorPG6 (join6 j k))
def gramTablePG6 : Matrix (Fin 4) (Fin 4) G :=
  !![⟨32,0⟩,⟨0,-16⟩,⟨0,-32⟩,⟨16,0⟩;
     ⟨0,16⟩,⟨32,0⟩,⟨16,0⟩,⟨0,32⟩;
     ⟨0,32⟩,⟨16,0⟩,⟨32,0⟩,⟨0,16⟩;
     ⟨16,0⟩,⟨0,-32⟩,⟨0,-16⟩,⟨32,0⟩]

theorem gramPG6_checked : ∀ i j, gramPG6 i j = gramTablePG6 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem reducedPG6_gram (i j : Fin 4) :
    reduced firstTwo6 (Physical.seed (pgRaw I)) (pairEquiv6 i) (pairEquiv6 j) =
      (1/128 : ℂ) * (gramTablePG6 i j : ℂ) := by
  rw [reduced6_index]
  simp_rw [pgseed6_index]
  have hi (k : Fin 64) : (pg6A k : ℂ) + I * (pg6B k : ℂ) = (numeratorPG6 k : ℂ) := by
    simp [numeratorPG6, map_add, map_mul]
  simp_rw [hi, star_mul]
  calc
    _ = (scale 6 * star (scale 6)) * (gramPG6 i j : ℂ) := by
      simp only [gramPG6, map_sum, map_mul, GaussianInt.toComplex_star,
        Complex.star_def, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [scale_norm, gramPG6_checked]; norm_num

def rhoMatrix5 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/4,I/16,-I/8,-1/16;
     -I/16,1/4,-1/16,I/8;
     I/8,-1/16,1/4,-I/16;
     -1/16,-I/8,I/16,1/4]

def rhoMatrix6 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/4,0,-I/8,0;
     0,1/4,0,I/8;
     I/8,0,1/4,0;
     0,-I/8,0,1/4]

def rhoMatrixPG6 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1/4,-I/8,-I/4,1/8;
     I/8,1/4,1/8,I/4;
     I/4,1/8,1/4,I/8;
     1/8,-I/4,-I/8,1/4]

/-- 与原统一种子真实两体约化矩阵逐项相等。 -/
theorem reduced5_matrix :
    (reduced firstTwo5 (Physical.seed (UnifiedEJM.rawPhase I))).submatrix
      pairEquiv5 pairEquiv5 = rhoMatrix5 := by
  ext i j
  rw [Matrix.submatrix_apply, reduced5_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [gramTable5,rhoMatrix5,GaussianInt.toComplex_def] <;> ring

theorem reduced6_matrix :
    (reduced firstTwo6 (Physical.seed (UnifiedEJM.rawPhase I))).submatrix
      pairEquiv6 pairEquiv6 = rhoMatrix6 := by
  ext i j
  rw [Matrix.submatrix_apply, reduced6_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [gramTable6,rhoMatrix6,GaussianInt.toComplex_def] <;> ring

theorem reducedPG6_matrix :
    (reduced firstTwo6 (Physical.seed (pgRaw I))).submatrix
      pairEquiv6 pairEquiv6 = rhoMatrixPG6 := by
  ext i j
  rw [Matrix.submatrix_apply, reducedPG6_gram]
  fin_cases i <;> fin_cases j <;>
    norm_num [gramTablePG6,rhoMatrixPG6,GaussianInt.toComplex_def] <;> ring

theorem rhoMatrix5_det (x : ℂ) :
    Matrix.det (x • 1 - rhoMatrix5) = (x-1/8)^2*(x-1/4)*(x-1/2) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [rhoMatrix5, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.succAbove]
  ring_nf
  simp
  ring

theorem rhoMatrix6_det (x : ℂ) :
    Matrix.det (x • 1 - rhoMatrix6) = (x-1/8)^2*(x-3/8)^2 := by
  rw [Matrix.det_succ_row_zero]
  norm_num [rhoMatrix6, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.succAbove]
  ring_nf
  simp
  ring

theorem rhoMatrixPG6_det (x : ℂ) :
    Matrix.det (x • 1 - rhoMatrixPG6) = x^2*(x-1/4)*(x-3/4) := by
  rw [Matrix.det_succ_row_zero]
  norm_num [rhoMatrixPG6, Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, Fin.succAbove]
  ring_nf
  simp
  ring

/-- 行列同时按同一计算基重排不改变实际约化态的特征多项式。 -/
lemma det_reduced_reindex {n : ℕ} {S : Finset (Fin n)}
    (e : Fin 4 ≃ Side S) (ψ : Vec n) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (hM : (reduced S ψ).submatrix e e = M) (x : ℂ) :
    Matrix.det (x • 1 - reduced S ψ) = Matrix.det (x • 1 - M) := by
  have h := Matrix.det_submatrix_equiv_self e (x • 1 - reduced S ψ)
  have hm : (x • 1 - reduced S ψ).submatrix e e = x • 1 - M := by
    rw [← hM]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [hm] at h
  exact h.symm

/-- 论文所用n=5实际零半径种子的两体特征多项式。 -/
theorem new5_endpoint_characteristic (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo5 (UnifiedEJM.seed 5 (Real.pi/2))) =
      (x-1/8)^2*(x-1/4)*(x-1/2) := by
  have hs : UnifiedEJM.seed 5 (Real.pi/2) = Physical.seed (UnifiedEJM.rawPhase I) := by
    simp [UnifiedEJM.seed,Physical.seed,anglePhase]
  rw [hs, det_reduced_reindex pairEquiv5 _ _ reduced5_matrix, rhoMatrix5_det]

/-- 论文所用n=6实际零半径种子的两体特征多项式。 -/
theorem new6_endpoint_characteristic (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo6 (UnifiedEJM.seed 6 (Real.pi/2))) =
      (x-1/8)^2*(x-3/8)^2 := by
  have hs : UnifiedEJM.seed 6 (Real.pi/2) = Physical.seed (UnifiedEJM.rawPhase I) := by
    simp [UnifiedEJM.seed,Physical.seed,anglePhase]
  rw [hs, det_reduced_reindex pairEquiv6 _ _ reduced6_matrix, rhoMatrix6_det]

/-- PG余弦族alpha=pi/2的实际电路种子两体特征多项式。 -/
theorem pg6_endpoint_characteristic (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo6 (EvenFamily.seed 6 (Real.pi/2) 0)) =
      x^2*(x-1/4)*(x-3/4) := by
  rw [pg_seed_eq]
  have ha : anglePhase (Real.pi/2) = I := by simp [anglePhase]
  rw [ha, det_reduced_reindex pairEquiv6 _ _ reducedPG6_matrix, rhoMatrixPG6_det]

theorem new5_endpoint_spectrum (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo5 (UnifiedEJM.seed 5 (Real.pi/2))) = 0 ↔
      x = 1/8 ∨ x = 1/4 ∨ x = 1/2 := by
  rw [new5_endpoint_characteristic]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]

theorem new6_endpoint_spectrum (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo6 (UnifiedEJM.seed 6 (Real.pi/2))) = 0 ↔
      x = 1/8 ∨ x = 3/8 := by
  rw [new6_endpoint_characteristic]
  simp [mul_eq_zero, sub_eq_zero]

theorem pg6_endpoint_spectrum (x : ℂ) :
    Matrix.det (x • 1 - reduced firstTwo6 (EvenFamily.seed 6 (Real.pi/2) 0)) = 0 ↔
      x = 0 ∨ x = 1/4 ∨ x = 3/4 := by
  rw [pg6_endpoint_characteristic]
  simp [mul_eq_zero, sub_eq_zero, or_assoc]

end UnifiedEJM.PhysicsSpectra
