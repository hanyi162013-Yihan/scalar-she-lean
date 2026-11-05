module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic
public import SHE.LocalHaar
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

set_option autoImplicit false

/-!
# Signed finite Haar transport and its spatial analytic ingredients

This file proves the finite, dimension-independent Frobenius estimate behind
the signed prefix estimate in Section 2.  The proof uses the exact difference
of two covariance matrices.  It does not replace that difference by the sum
of the separate covariances, and requires no differentiability of Cholesky
factorization.

It also constructs the finite weighted Haar basis and its actual reference
factor, literal periodic step fields, the fractional Fourier inverse
inequality, and the circle heat/detail projection estimate. The signed
negative-input prefix and heat assembly are proved in `SHE.SignedPrefix`.
The arbitrary-coefficient infinite-factor passage remains an explicit limit
identification problem, rather than an assumption of a transport estimate.
-/

noncomputable section
namespace SHE
namespace FiniteTransport

open Finset Matrix

variable {ι κ τ : Type*}

/-- Squared Euclidean norm, written as a finite sum to expose all constants. -/
def vectorSq [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, (x i) ^ 2

/-- Squared Frobenius norm. -/
def frobeniusSq [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) : ℝ :=
  ∑ i, ∑ j, (A i j) ^ 2

theorem vectorSq_nonneg [Fintype ι] (x : ι → ℝ) : 0 ≤ vectorSq x := by
  exact sum_nonneg fun i _ => sq_nonneg (x i)

theorem frobeniusSq_nonneg [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    0 ≤ frobeniusSq A := by
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg (A i j)

theorem frobeniusSq_transpose [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    frobeniusSq Aᵀ = frobeniusSq A := by
  unfold frobeniusSq
  exact sum_comm

/-- An operator bound on vectors applies column by column, without a dimension loss. -/
theorem frobeniusSq_mul_le [Fintype ι] [Fintype κ] [Fintype τ]
    (A : Matrix ι κ ℝ) (B : Matrix κ τ ℝ) (K : ℝ)
    (hA : ∀ x : κ → ℝ, vectorSq (A *ᵥ x) ≤ K * vectorSq x) :
    frobeniusSq (A * B) ≤ K * frobeniusSq B := by
  calc
    _ = ∑ j, vectorSq (A *ᵥ (fun i => B i j)) := by
      simp only [frobeniusSq, vectorSq, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      exact sum_comm
    _ ≤ ∑ j, K * vectorSq (fun i => B i j) :=
      sum_le_sum fun j _ => hA (fun i => B i j)
    _ = K * frobeniusSq B := by
      rw [← mul_sum]
      congr 1
      exact sum_comm

/-- The corresponding row estimate uses the vector bound for the transpose. -/
theorem frobeniusSq_mul_le_right [Fintype ι] [Fintype κ] [Fintype τ]
    (A : Matrix ι κ ℝ) (B : Matrix τ κ ℝ) (K : ℝ)
    (hB : ∀ x : κ → ℝ, vectorSq (B *ᵥ x) ≤ K * vectorSq x) :
    frobeniusSq (A * Bᵀ) ≤ K * frobeniusSq A := by
  rw [← frobeniusSq_transpose (A * Bᵀ), Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simpa only [frobeniusSq_transpose] using frobeniusSq_mul_le B Aᵀ K hB

/-- Euclidean operator bounds are invariant under transpose.  This is proved
from the finite Cauchy--Schwarz inequality, so it introduces no matrix norm
or dimension-dependent comparison constant. -/
theorem transpose_vectorSq_le [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hA : ∀ x : κ → ℝ, vectorSq (A *ᵥ x) ≤ K * vectorSq x)
    (x : ι → ℝ) :
    vectorSq (Aᵀ *ᵥ x) ≤ K * vectorSq x := by
  let y := Aᵀ *ᵥ x
  have hcs : (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ vectorSq x * vectorSq (A *ᵥ y) := by
    simpa only [dotProduct, vectorSq, Finset.mem_univ, forall_const, sum_attach] using
      sum_mul_sq_le_sq_mul_sq (univ : Finset ι) x (A *ᵥ y)
  have heq : x ⬝ᵥ (A *ᵥ y) = vectorSq y := by
    rw [← Matrix.dotProduct_transpose_mulVec A y x]
    simp only [y, dotProduct, vectorSq, pow_two]
  rw [heq] at hcs
  have hh := mul_le_mul_of_nonneg_left (hA y) (vectorSq_nonneg x)
  have hmul : vectorSq y * vectorSq y ≤ (K * vectorSq x) * vectorSq y := by
    nlinarith only [hcs, hh]
  by_cases hy : vectorSq y = 0
  · change vectorSq y ≤ K * vectorSq x
    rw [hy]
    exact mul_nonneg hK (vectorSq_nonneg x)
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (vectorSq_nonneg y) (Ne.symm hy))).1 hmul

/-- The diagonal of a product of lower triangular matrices is the product of
their diagonals. -/
theorem lower_mul_diag [Fintype ι] [LinearOrder ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular)
    (i : ι) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply sum_eq_single i
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [hB hji, mul_zero]
    · rw [hA hij, zero_mul]
  · simp

/-- Triangular splitting is a contraction in Frobenius norm whenever the two
diagonal contributions have the same sign. -/
theorem lower_split_frobeniusSq_le [Fintype ι] [LinearOrder ι]
    (X Y : Matrix ι ι ℝ) (hX : X.IsLowerTriangular) (hY : Y.IsLowerTriangular)
    (hdiag : ∀ i, 0 ≤ X i i * Y i i) :
    frobeniusSq X ≤ frobeniusSq (X + Yᵀ) := by
  apply sum_le_sum
  intro i hi
  apply sum_le_sum
  intro j hj
  change (X i j) ^ 2 ≤ (X i j + Y j i) ^ 2
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [hX hij]
    simpa using sq_nonneg (Y j i)
  · nlinarith [sq_nonneg (Y i i), hdiag i]
  · rw [hY hji, add_zero]

/-- A lower energy bound controls the inverse on every vector. -/
theorem inverse_vectorSq_le [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) [Invertible A] (m : ℝ) (hm : 0 < m)
    (hA : ∀ x : ι → ℝ, m * vectorSq x ≤ vectorSq (A *ᵥ x))
    (x : ι → ℝ) :
    vectorSq (A⁻¹ *ᵥ x) ≤ m⁻¹ * vectorSq x := by
  have h := hA (A⁻¹ *ᵥ x)
  simp only [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec] at h
  have h' : vectorSq (A⁻¹ *ᵥ x) ≤ vectorSq x / m :=
    (le_div_iff₀ hm).2 (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using h'

/-- The quadratic form of a covariance is exactly the energy of the
transposed factor. -/
theorem covariance_energy [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (x : ι → ℝ) :
    vectorSq (Aᵀ *ᵥ x) = x ⬝ᵥ ((A * Aᵀ) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.dotProduct_transpose_mulVec A]
  simp only [vectorSq, dotProduct, pow_two]

/-- An upper covariance bound controls the factor with the same constant. -/
theorem factor_upper_of_covariance [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hcov : ∀ x : ι → ℝ, x ⬝ᵥ ((A * Aᵀ) *ᵥ x) ≤ U * vectorSq x)
    (x : κ → ℝ) : vectorSq (A *ᵥ x) ≤ U * vectorSq x := by
  have hT : ∀ y : ι → ℝ, vectorSq (Aᵀ *ᵥ y) ≤ U * vectorSq y := by
    intro y
    rw [covariance_energy]
    exact hcov y
  simpa only [Matrix.transpose_transpose] using transpose_vectorSq_le Aᵀ U hU hT x

/-- A lower covariance bound controls an invertible square factor with the
same constant.  No spectral theorem or loss depending on dimension is used. -/
theorem factor_lower_of_covariance [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) [Invertible A] (m : ℝ) (hm : 0 < m)
    (hcov : ∀ x : ι → ℝ, m * vectorSq x ≤ x ⬝ᵥ ((A * Aᵀ) *ᵥ x))
    (x : ι → ℝ) : m * vectorSq x ≤ vectorSq (A *ᵥ x) := by
  have hT : ∀ y : ι → ℝ, m * vectorSq y ≤ vectorSq (Aᵀ *ᵥ y) := by
    intro y
    rw [covariance_energy]
    exact hcov y
  have hTi : ∀ y : ι → ℝ, vectorSq ((A⁻¹)ᵀ *ᵥ y) ≤ m⁻¹ * vectorSq y := by
    simpa only [Matrix.transpose_nonsing_inv] using inverse_vectorSq_le Aᵀ m hm hT
  have hAi := transpose_vectorSq_le (A⁻¹)ᵀ m⁻¹ (inv_nonneg.mpr hm.le) hTi (A *ᵥ x)
  simp only [Matrix.transpose_transpose, Matrix.mulVec_mulVec,
    Matrix.inv_mul_of_invertible, Matrix.one_mulVec] at hAi
  have hdiv : vectorSq x ≤ vectorSq (A *ᵥ x) / m := by
    simpa only [div_eq_mul_inv, mul_comm] using hAi
  simpa only [mul_comm] using (le_div_iff₀ hm).1 hdiv

/-- Positivity of the Cholesky diagonal is preserved by inversion. -/
theorem inverse_lower_diag_pos [Fintype ι] [LinearOrder ι]
    (A : Matrix ι ι ℝ) [Invertible A] (hA : A.IsLowerTriangular)
    (hpos : ∀ i, 0 < A i i) (i : ι) : 0 < A⁻¹ i i := by
  have hi : A⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hA
  have hp := lower_mul_diag A⁻¹ A hi hA i
  simp only [Matrix.inv_mul_of_invertible, Matrix.one_apply_eq] at hp
  nlinarith [hpos i]

/-- Exact signed covariance identity, with no interpolation or limiting argument. -/
theorem signed_covariance_identity [Fintype ι] [DecidableEq ι]
    (L M : Matrix ι ι ℝ) [Invertible L] [Invertible M] :
    L⁻¹ * (L * Lᵀ - M * Mᵀ) * (M⁻¹)ᵀ =
      L⁻¹ * (L - M) + (M⁻¹ * (L - M))ᵀ := by
  have hdiff : L * Lᵀ - M * Mᵀ = (L - M) * Mᵀ + L * (L - M)ᵀ := by
    rw [Matrix.transpose_sub]
    noncomm_ring
  rw [hdiff]
  calc
    _ = (L⁻¹ * (L - M)) * (Mᵀ * (M⁻¹)ᵀ) +
        ((L⁻¹ * L) * (L - M)ᵀ) * (M⁻¹)ᵀ := by noncomm_ring
    _ = _ := by
      simp only [← Matrix.transpose_mul, Matrix.inv_mul_of_invertible,
        Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]

/-- The transformed signed covariance controls the transformed factor
difference in Frobenius norm.  The diagonal sign condition is proved from
the positive Cholesky diagonals. -/
theorem signed_covariance_frobeniusSq_le [Fintype ι] [LinearOrder ι]
    (L M : Matrix ι ι ℝ) [Invertible L] [Invertible M]
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLp : ∀ i, 0 < L i i) (hMp : ∀ i, 0 < M i i) :
    frobeniusSq (L⁻¹ * (L - M)) ≤
      frobeniusSq (L⁻¹ * (L * Lᵀ - M * Mᵀ) * (M⁻¹)ᵀ) := by
  have hLi : L⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hL
  have hMi : M⁻¹.IsLowerTriangular := Matrix.blockTriangular_inv_of_blockTriangular hM
  have hD : (L - M).IsLowerTriangular := hL.sub hM
  rw [signed_covariance_identity]
  apply lower_split_frobeniusSq_le _ _ (hLi.mul hD) (hMi.mul hD)
  intro i
  rw [lower_mul_diag _ _ hLi hD, lower_mul_diag _ _ hMi hD]
  have hp : 0 ≤ (L⁻¹ i i * M⁻¹ i i) * ((L - M) i i) ^ 2 :=
    mul_nonneg (mul_nonneg (inverse_lower_diag_pos L hL hLp i).le
      (inverse_lower_diag_pos M hM hMp i).le) (sq_nonneg _)
  nlinarith only [hp]

/-- Dimension-independent finite signed Cholesky estimate.

`m` and `U` are lower/upper squared operator bounds.  The hypotheses contain
only triangularity, positive diagonal, and the usual uniform energy bounds;
the signed difference estimate is the conclusion.  In particular, the
constant `U / m^2` has no dependence on the number of rows.
-/
theorem cholesky_signed_frobeniusSq [Fintype ι] [LinearOrder ι]
    (L M : Matrix ι ι ℝ) (m U : ℝ) (hm : 0 < m) (hU : 0 ≤ U)
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLp : ∀ i, 0 < L i i) (hMp : ∀ i, 0 < M i i)
    (hLupper : ∀ x : ι → ℝ, vectorSq (L *ᵥ x) ≤ U * vectorSq x)
    (hLlower : ∀ x : ι → ℝ, m * vectorSq x ≤ vectorSq (L *ᵥ x))
    (hMlower : ∀ x : ι → ℝ, m * vectorSq x ≤ vectorSq (M *ᵥ x)) :
    frobeniusSq (L - M) ≤ U / m ^ 2 * frobeniusSq (L * Lᵀ - M * Mᵀ) := by
  have hLd : IsUnit L.det := isUnit_iff_ne_zero.2 <|
    (hL.det_ne_zero_iff).2 fun i => (hLp i).ne'
  have hMd : IsUnit M.det := isUnit_iff_ne_zero.2 <|
    (hM.det_ne_zero_iff).2 fun i => (hMp i).ne'
  let : Invertible L := Matrix.invertibleOfIsUnitDet L hLd
  let : Invertible M := Matrix.invertibleOfIsUnitDet M hMd
  have hLi := inverse_vectorSq_le L m hm hLlower
  have hMi := inverse_vectorSq_le M m hm hMlower
  have hsplit := signed_covariance_frobeniusSq_le L M hL hM hLp hMp
  have hright := frobeniusSq_mul_le_right (L * Lᵀ - M * Mᵀ) M⁻¹ m⁻¹ hMi
  have hleft := frobeniusSq_mul_le L⁻¹
    ((L * Lᵀ - M * Mᵀ) * (M⁻¹)ᵀ) m⁻¹ hLi
  have hstart := frobeniusSq_mul_le L (L⁻¹ * (L - M)) U hLupper
  simp only [Matrix.mul_inv_cancel_left_of_invertible] at hstart
  rw [← Matrix.mul_assoc] at hleft
  have hi : 0 ≤ m⁻¹ := inv_nonneg.mpr hm.le
  calc
    frobeniusSq (L - M) ≤ U * frobeniusSq (L⁻¹ * (L - M)) := hstart
    _ ≤ U * frobeniusSq (L⁻¹ * (L * Lᵀ - M * Mᵀ) * (M⁻¹)ᵀ) :=
      mul_le_mul_of_nonneg_left hsplit hU
    _ ≤ U * (m⁻¹ * frobeniusSq ((L * Lᵀ - M * Mᵀ) * (M⁻¹)ᵀ)) :=
      mul_le_mul_of_nonneg_left hleft hU
    _ ≤ U * (m⁻¹ * (m⁻¹ * frobeniusSq (L * Lᵀ - M * Mᵀ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hright hi) hU
    _ = _ := by field_simp

/-- The finite signed transport estimate stated directly in terms of the
covariance ellipticity assumptions used in the manuscript. -/
theorem cholesky_signed_frobeniusSq_of_covariance [Fintype ι] [LinearOrder ι]
    (L M : Matrix ι ι ℝ) (m U : ℝ) (hm : 0 < m) (hU : 0 ≤ U)
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLp : ∀ i, 0 < L i i) (hMp : ∀ i, 0 < M i i)
    (hLupper : ∀ x : ι → ℝ, x ⬝ᵥ ((L * Lᵀ) *ᵥ x) ≤ U * vectorSq x)
    (hLlower : ∀ x : ι → ℝ, m * vectorSq x ≤ x ⬝ᵥ ((L * Lᵀ) *ᵥ x))
    (hMlower : ∀ x : ι → ℝ, m * vectorSq x ≤ x ⬝ᵥ ((M * Mᵀ) *ᵥ x)) :
    frobeniusSq (L - M) ≤ U / m ^ 2 * frobeniusSq (L * Lᵀ - M * Mᵀ) := by
  have hLd : IsUnit L.det := isUnit_iff_ne_zero.2 <|
    (hL.det_ne_zero_iff).2 fun i => (hLp i).ne'
  have hMd : IsUnit M.det := isUnit_iff_ne_zero.2 <|
    (hM.det_ne_zero_iff).2 fun i => (hMp i).ne'
  let : Invertible L := Matrix.invertibleOfIsUnitDet L hLd
  let : Invertible M := Matrix.invertibleOfIsUnitDet M hMd
  exact cholesky_signed_frobeniusSq L M m U hm hU hL hM hLp hMp
    (factor_upper_of_covariance L U hU hLupper)
    (factor_lower_of_covariance L m hm hLlower)
    (factor_lower_of_covariance M m hm hMlower)

end FiniteTransport

/-! ## Explicit weighted Haar columns on finite binary grids -/

namespace FiniteHaar

open Finset Matrix

/-- The leaves of a complete binary tree of depth `n`. -/
def Grid : ℕ → Type
  | 0 => Unit
  | n + 1 => Grid n ⊕ Grid n

/-- One index for each nonconstant Haar column, including the root split. -/
def DetailIndex : ℕ → Type
  | 0 => Empty
  | n + 1 => Unit ⊕ (DetailIndex n ⊕ DetailIndex n)

abbrev gridFintype : (n : ℕ) → Fintype (Grid n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    let : Fintype (Grid n) := gridFintype n
    exact inferInstanceAs (Fintype (Grid n ⊕ Grid n))

abbrev detailFintype : (n : ℕ) → Fintype (DetailIndex n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n + 1 => by
    let : Fintype (DetailIndex n) := detailFintype n
    exact inferInstanceAs (Fintype (Unit ⊕ (DetailIndex n ⊕ DetailIndex n)))

attribute [reducible] Grid
attribute [instance] gridFintype detailFintype

instance (n : ℕ) : DecidableEq (Grid n) := Classical.decEq _
instance (n : ℕ) : DecidableEq (DetailIndex n) := Classical.decEq _

def firstLeaf : (n : ℕ) → Grid n
  | 0 => ()
  | n + 1 => Sum.inl (firstLeaf n)

instance (n : ℕ) : Nonempty (Grid n) := ⟨firstLeaf n⟩

/-- Counting-measure mass; normalized dyadic cell weights can be included in `c`. -/
def totalMass (n : ℕ) (c : Grid n → ℝ) : ℝ := ∑ x, c x

theorem totalMass_pos (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x) :
    0 < totalMass n c := by
  exact sum_pos (fun x _ => hc x) univ_nonempty

theorem totalMass_succ (n : ℕ) (c : Grid (n + 1) → ℝ) :
    totalMass (n + 1) c =
      totalMass n (fun x => c (Sum.inl x)) + totalMass n (fun x => c (Sum.inr x)) := by
  exact Fintype.sum_sum_type c

/-- Explicit local mass formula, recursively extended by zero away from its node. -/
def detailColumn : (n : ℕ) → (Grid n → ℝ) → DetailIndex n → Grid n → ℝ
  | 0, _, k => nomatch k
  | n + 1, c, Sum.inl _ =>
    Sum.elim
      (fun _ => haarLeft (totalMass n (fun x => c (Sum.inl x)))
        (totalMass n (fun x => c (Sum.inr x))))
      (fun _ => haarRight (totalMass n (fun x => c (Sum.inl x)))
        (totalMass n (fun x => c (Sum.inr x))))
  | n + 1, c, Sum.inr (Sum.inl k) =>
    Sum.elim (detailColumn n (fun x => c (Sum.inl x)) k) (fun _ => 0)
  | n + 1, c, Sum.inr (Sum.inr k) =>
    Sum.elim (fun _ => 0) (detailColumn n (fun x => c (Sum.inr x)) k)

/-- `none` is the constant column; `some k` is the corresponding detail. -/
def haarColumn (n : ℕ) (c : Grid n → ℝ) : Option (DetailIndex n) → Grid n → ℝ
  | none => fun _ => (Real.sqrt (totalMass n c))⁻¹
  | some k => detailColumn n c k

def weightedMean {α : Type*} [Fintype α] (c u : α → ℝ) : ℝ := ∑ x, c x * u x

def weightedInner {α : Type*} [Fintype α] (c u v : α → ℝ) : ℝ :=
  ∑ x, c x * (u x * v x)

theorem weightedMean_const {α : Type*} [Fintype α] (c : α → ℝ) (a : ℝ) :
    weightedMean c (fun _ => a) = (∑ x, c x) * a := by
  exact (sum_mul ..).symm

@[simp] theorem weightedMean_zero {α : Type*} [Fintype α] (c : α → ℝ) :
    weightedMean c (fun _ => 0) = 0 := by simp [weightedMean]

theorem weightedMean_sum {α β : Type*} [Fintype α] [Fintype β]
    (c : α ⊕ β → ℝ) (u : α → ℝ) (v : β → ℝ) :
    weightedMean c (Sum.elim u v) = weightedMean (fun x => c (Sum.inl x)) u +
      weightedMean (fun x => c (Sum.inr x)) v := by
  simp only [weightedMean, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem weightedInner_const_left {α : Type*} [Fintype α]
    (c : α → ℝ) (a : ℝ) (u : α → ℝ) :
    weightedInner c (fun _ => a) u = a * weightedMean c u := by
  unfold weightedInner weightedMean
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

theorem weightedInner_const_right {α : Type*} [Fintype α]
    (c u : α → ℝ) (a : ℝ) :
    weightedInner c u (fun _ => a) = a * weightedMean c u := by
  unfold weightedInner weightedMean
  rw [mul_sum]
  apply sum_congr rfl
  intro x hx
  ring

theorem weightedInner_const_const {α : Type*} [Fintype α]
    (c : α → ℝ) (a b : ℝ) :
    weightedInner c (fun _ => a) (fun _ => b) = (∑ x, c x) * (a * b) := by
  exact (sum_mul ..).symm

@[simp] theorem weightedInner_zero_left {α : Type*} [Fintype α] (c u : α → ℝ) :
    weightedInner c (fun _ => 0) u = 0 := by simp [weightedInner]

@[simp] theorem weightedInner_zero_right {α : Type*} [Fintype α] (c u : α → ℝ) :
    weightedInner c u (fun _ => 0) = 0 := by simp [weightedInner]

theorem weightedInner_sum {α β : Type*} [Fintype α] [Fintype β]
    (c : α ⊕ β → ℝ) (u u' : α → ℝ) (v v' : β → ℝ) :
    weightedInner c (Sum.elim u v) (Sum.elim u' v') =
      weightedInner (fun x => c (Sum.inl x)) u u' +
      weightedInner (fun x => c (Sum.inr x)) v v' := by
  simp only [weightedInner, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

/-- Every detail has weighted mean zero, at every depth. -/
theorem detailColumn_cancellation (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (k : DetailIndex n) : weightedMean c (detailColumn n c k) = 0 := by
  induction n with
  | zero => exact Empty.elim k
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at c hc k ⊢
    rcases k with k | (k | k)
    · simp only [detailColumn]
      erw [weightedMean_sum]
      rw [weightedMean_const, weightedMean_const]
      exact haar_cancellation (totalMass_pos n _ (fun x => hc (Sum.inl x)))
        (totalMass_pos n _ (fun x => hc (Sum.inr x)))
    · simp only [detailColumn]
      erw [weightedMean_sum]
      rw [weightedMean_zero, add_zero]
      exact ih _ (fun x => hc (Sum.inl x)) k
    · simp only [detailColumn]
      erw [weightedMean_sum]
      rw [weightedMean_zero, zero_add]
      exact ih _ (fun x => hc (Sum.inr x)) k

/-- All explicitly constructed detail columns are orthonormal in the weighted
finite space.  This includes columns in disjoint branches and ancestor/child
columns, rather than just the two-child normalization calculation. -/
theorem detailColumn_orthonormal (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (k j : DetailIndex n) :
    weightedInner c (detailColumn n c k) (detailColumn n c j) = if k = j then 1 else 0 := by
  induction n with
  | zero => exact Empty.elim k
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at c hc k j ⊢
    have hcl : ∀ x, 0 < c (Sum.inl x) := fun x => hc (Sum.inl x)
    have hcr : ∀ x, 0 < c (Sum.inr x) := fun x => hc (Sum.inr x)
    rcases k with ⟨⟩ | (k | k) <;> rcases j with ⟨⟩ | (j | j)
    all_goals simp only [detailColumn]
    all_goals erw [weightedInner_sum]
    all_goals simp only [weightedInner_zero_left, weightedInner_zero_right,
      add_zero, zero_add, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]
    · rw [weightedInner_const_const, weightedInner_const_const]
      simpa only [totalMass, pow_two] using
        haar_normalization (totalMass_pos n _ hcl) (totalMass_pos n _ hcr)
    · rw [weightedInner_const_left, detailColumn_cancellation n _ hcl]
      simp
    · rw [weightedInner_const_left, detailColumn_cancellation n _ hcr]
      simp
    · rw [weightedInner_const_right, detailColumn_cancellation n _ hcl]
      simp
    · exact ih _ hcl k j
    · rw [weightedInner_const_right, detailColumn_cancellation n _ hcr]
      simp
    · exact ih _ hcr k j

theorem inv_sqrt_mul_self {m : ℝ} (hm : 0 < m) :
    (Real.sqrt m)⁻¹ * (Real.sqrt m)⁻¹ = m⁻¹ := by
  rw [← _root_.mul_inv_rev, Real.mul_self_sqrt hm.le]

/-- The constant and every detail form an orthonormal family. -/
theorem haarColumn_orthonormal (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (k j : Option (DetailIndex n)) :
    weightedInner c (haarColumn n c k) (haarColumn n c j) = if k = j then 1 else 0 := by
  cases k with
  | none =>
    cases j with
    | none =>
      simp only [haarColumn, ite_true, weightedInner_const_const]
      rw [inv_sqrt_mul_self (totalMass_pos n c hc)]
      exact mul_inv_cancel₀ (totalMass_pos n c hc).ne'
    | some j =>
      simp only [haarColumn, reduceCtorEq, ite_false, weightedInner_const_left,
        detailColumn_cancellation n c hc j, mul_zero]
  | some k =>
    cases j with
    | none =>
      simp only [haarColumn, reduceCtorEq, ite_false, weightedInner_const_right,
        detailColumn_cancellation n c hc k, mul_zero]
    | some j =>
      simpa only [haarColumn, Option.some.injEq] using detailColumn_orthonormal n c hc k j

theorem card_grid (n : ℕ) : Fintype.card (Grid n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Grid n ⊕ Grid n) = _
    erw [Fintype.card_sum]
    rw [ih, pow_succ]
    omega

/-- The finite orthonormal family has exactly as many columns as leaves. -/
theorem card_modes (n : ℕ) : Fintype.card (Option (DetailIndex n)) = Fintype.card (Grid n) := by
  have h : Fintype.card (DetailIndex n) + 1 = Fintype.card (Grid n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change Fintype.card (Unit ⊕ (DetailIndex n ⊕ DetailIndex n)) + 1 =
        Fintype.card (Grid n ⊕ Grid n)
      erw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum]
      simp only [Fintype.card_unique]
      omega
  simpa only [Fintype.card_option] using h

/-- The weighted Haar functions, as columns in the leaf coordinate system. -/
def haarMatrix (n : ℕ) (c : Grid n → ℝ) :
    Matrix (Grid n) (Option (DetailIndex n)) ℝ := fun x k => haarColumn n c k x

/-- The finite local factor has columns exactly `c * χ`. -/
def localFactor (n : ℕ) (c : Grid n → ℝ) :
    Matrix (Grid n) (Option (DetailIndex n)) ℝ := Matrix.diagonal c * haarMatrix n c

@[simp] theorem localFactor_apply (n : ℕ) (c : Grid n → ℝ)
    (x : Grid n) (k : Option (DetailIndex n)) :
    localFactor n c x k = c x * haarColumn n c k x := by
  simp [localFactor, haarMatrix]

theorem haarMatrix_transpose_mul_localFactor (n : ℕ) (c : Grid n → ℝ)
    (hc : ∀ x, 0 < c x) :
    (haarMatrix n c)ᵀ * localFactor n c = 1 := by
  ext k j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, haarMatrix, localFactor_apply]
  have h := haarColumn_orthonormal n c hc k j
  simp only [weightedInner] at h
  convert h using 1
  · apply sum_congr rfl
    intro x hx
    ring
  · simp only [Matrix.one_apply]

/-- Completeness follows from the proved orthogonality and the exact finite
cardinality.  It is not an assumed basis property. -/
theorem localFactor_mul_haarMatrix_transpose (n : ℕ) (c : Grid n → ℝ)
    (hc : ∀ x, 0 < c x) :
    localFactor n c * (haarMatrix n c)ᵀ = 1 := by
  exact (Matrix.mul_eq_one_comm_of_card_eq _ _ ℝ (card_modes n)).1
    (haarMatrix_transpose_mul_localFactor n c hc)

/-- Exact covariance factorization on every finite binary grid.
This is the finite form of the manuscript's `L L* = M_c` identity. -/
theorem localFactor_covariance (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x) :
    localFactor n c * (localFactor n c)ᵀ = Matrix.diagonal c := by
  calc
    _ = (localFactor n c * (haarMatrix n c)ᵀ) * Matrix.diagonal c := by
      simp only [localFactor, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = _ := by rw [localFactor_mul_haarMatrix_transpose n c hc, Matrix.one_mul]

end FiniteHaar

/-! ## Spatial translation and fractional inverse estimates in a cyclic step model -/

namespace CyclicStep

open Finset MeasureTheory Set
open FiniteTransport

variable {α : Type*} [Fintype α]

/-- Translation difference at an integral number of cells. -/
def shiftSq (σ : Equiv.Perm α) (f : α → ℝ) (q : ℕ) : ℝ :=
  vectorSq (fun x => f ((σ ^ q) x) - f x)

theorem shiftSq_nonneg (σ : Equiv.Perm α) (f : α → ℝ) (q : ℕ) :
    0 ≤ shiftSq σ f q := vectorSq_nonneg _

@[simp] theorem shiftSq_zero (σ : Equiv.Perm α) (f : α → ℝ) : shiftSq σ f 0 = 0 := by
  simp [shiftSq, vectorSq]

/-- A cyclic shift is an exact Euclidean isometry. -/
theorem vectorSq_perm (σ : Equiv.Perm α) (f : α → ℝ) :
    vectorSq (fun x => f (σ x)) = vectorSq f := by
  exact Equiv.sum_comp σ (fun x => (f x) ^ 2)

/-- Every integral-cell translation has difference energy at most four times
the original energy, with no dependence on the number of cells. -/
theorem shiftSq_le_four (σ : Equiv.Perm α) (f : α → ℝ) (q : ℕ) :
    shiftSq σ f q ≤ 4 * vectorSq f := by
  have h : shiftSq σ f q ≤
      2 * vectorSq (fun x => f ((σ ^ q) x)) + 2 * vectorSq f := by
    unfold shiftSq vectorSq
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro x hx
    nlinarith [sq_nonneg (f ((σ ^ q) x) + f x)]
  rw [vectorSq_perm] at h
  linarith

/-- The exact overlap formula for a shift by a fractional number of equal
cells: the two overlap lengths are `1 - θ` and `θ`. -/
def translationSq (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) : ℝ :=
  (1 - (z - (⌊z⌋₊ : ℝ))) * shiftSq σ f ⌊z⌋₊ +
    (z - (⌊z⌋₊ : ℝ)) * shiftSq σ f (⌊z⌋₊ + 1)

theorem translationSq_nonneg (σ : Equiv.Perm α) (f : α → ℝ)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ translationSq σ f z := by
  have hθ : 0 ≤ z - (⌊z⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hz)
  have hθ1 : z - (⌊z⌋₊ : ℝ) < 1 := Nat.self_sub_floor_lt_one z
  exact add_nonneg (mul_nonneg (by linarith) (shiftSq_nonneg _ _ _))
    (mul_nonneg hθ (shiftSq_nonneg _ _ _))

theorem translationSq_le_four (σ : Equiv.Perm α) (f : α → ℝ)
    {z : ℝ} (hz : 0 ≤ z) : translationSq σ f z ≤ 4 * vectorSq f := by
  have hθ : 0 ≤ z - (⌊z⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hz)
  have hθ1 : z - (⌊z⌋₊ : ℝ) < 1 := Nat.self_sub_floor_lt_one z
  have h₁ := mul_le_mul_of_nonneg_left (shiftSq_le_four σ f ⌊z⌋₊)
    (show 0 ≤ 1 - (z - (⌊z⌋₊ : ℝ)) by linarith)
  have h₂ := mul_le_mul_of_nonneg_left (shiftSq_le_four σ f (⌊z⌋₊ + 1)) hθ
  unfold translationSq
  nlinarith only [h₁, h₂]

/-- This is the translation estimate used by the manuscript's step-function
Sobolev inverse argument.  It is proved here for the finite cyclic overlap
model, rather than postulated as a regularity hypothesis. -/
theorem translationSq_le_min (σ : Equiv.Perm α) (f : α → ℝ)
    {z : ℝ} (hz : 0 ≤ z) :
    translationSq σ f z ≤ 4 * min 1 z * vectorSq f := by
  by_cases hz1 : z < 1
  · have hfloor : ⌊z⌋₊ = 0 := Nat.floor_eq_zero.2 hz1
    simp only [translationSq, hfloor, Nat.cast_zero, sub_zero, shiftSq_zero,
      mul_zero, zero_add, min_eq_right hz1.le]
    nlinarith [mul_le_mul_of_nonneg_left (shiftSq_le_four σ f 1) hz]
  · rw [min_eq_left (by linarith : 1 ≤ z), mul_one]
    exact translationSq_le_four σ f hz

theorem measurable_translationSq (σ : Equiv.Perm α) (f : α → ℝ) :
    Measurable (translationSq σ f) := by
  have hf : Measurable (fun q : ℕ => shiftSq σ f q) := measurable_of_countable _
  have hf' : Measurable (fun q : ℕ => shiftSq σ f (q + 1)) := measurable_of_countable _
  have hfloor : Measurable (fun z : ℝ => (⌊z⌋₊ : ℝ)) :=
    (measurable_of_countable (fun q : ℕ => (q : ℝ))).comp Nat.measurable_floor
  exact ((measurable_const.sub (measurable_id.sub hfloor)).mul
    (hf.comp Nat.measurable_floor)).add
    ((measurable_id.sub hfloor).mul (hf'.comp Nat.measurable_floor))

/-- Integrable power majorant for fractional translation energy. -/
def fractionalKernel (ρ : ℝ) (z : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => x ^ (-2 * ρ)) z +
    (Ioi (1 : ℝ)).indicator (fun x => x ^ (-1 - 2 * ρ)) z

theorem fractionalKernel_nonneg (ρ z : ℝ) : 0 ≤ fractionalKernel ρ z := by
  unfold fractionalKernel
  apply add_nonneg
  · exact Set.indicator_nonneg (fun (x : ℝ) hx => Real.rpow_nonneg hx.1.le _) z
  · exact Set.indicator_nonneg
      (fun (x : ℝ) hx => Real.rpow_nonneg (zero_lt_one.trans hx).le _) z

theorem integrable_fractionalKernel {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Integrable (fractionalKernel ρ) := by
  have hs : IntegrableOn (fun z : ℝ => z ^ (-2 * ρ)) (Ioc (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -2 * ρ) :
      IntervalIntegrable (fun z : ℝ => z ^ (-2 * ρ)) volume 0 1).1
  have hl : IntegrableOn (fun z : ℝ => z ^ (-1 - 2 * ρ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  exact ((integrable_indicator_iff measurableSet_Ioc).2 hs).add
    ((integrable_indicator_iff measurableSet_Ioi).2 hl)

/-- The two singular tails are integrable exactly in the subcritical range
`0 < ρ < 1/2`; the explicit constant is retained. -/
theorem integral_fractionalKernel {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    ∫ z : ℝ, fractionalKernel ρ z = 1 / (1 - 2 * ρ) + 1 / (2 * ρ) := by
  have hs : IntegrableOn (fun z : ℝ => z ^ (-2 * ρ)) (Ioc (0 : ℝ) 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -2 * ρ) :
      IntervalIntegrable (fun z : ℝ => z ^ (-2 * ρ)) volume 0 1).1
  have hl : IntegrableOn (fun z : ℝ => z ^ (-1 - 2 * ρ)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  unfold fractionalKernel
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).2 hs)
      ((integrable_indicator_iff measurableSet_Ioi).2 hl),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith : -1 < -2 * ρ)),
    integral_Ioi_rpow_of_lt (by linarith : -1 - 2 * ρ < -1) zero_lt_one]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : -2 * ρ + 1 ≠ 0), sub_zero]
  congr 1 <;> ring

/-- The Gagliardo integrand, extended by zero to nonpositive shifts. -/
def fractionalIntegrand (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => translationSq σ f x * x ^ (-1 - 2 * ρ)) z

theorem measurable_fractionalIntegrand (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) :
    Measurable (fractionalIntegrand ρ σ f) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact (measurable_translationSq σ f).mul (by fun_prop)

theorem fractionalIntegrand_nonneg (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) :
    0 ≤ fractionalIntegrand ρ σ f z := by
  exact Set.indicator_nonneg (fun (x : ℝ) hx =>
    mul_nonneg (translationSq_nonneg σ f hx.le) (Real.rpow_nonneg hx.le _)) z

theorem fractionalIntegrand_le (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) :
    fractionalIntegrand ρ σ f z ≤ (4 * vectorSq f) * fractionalKernel ρ z := by
  by_cases hz : 0 < z
  · rw [fractionalIntegrand, Set.indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz)]
    have ht := mul_le_mul_of_nonneg_right (translationSq_le_min σ f hz.le)
      (Real.rpow_nonneg hz.le (-1 - 2 * ρ))
    by_cases hz1 : z ≤ 1
    · have hpower : z * z ^ (-1 - 2 * ρ) = z ^ (-2 * ρ) := by
        calc
          _ = z ^ (1 : ℝ) * z ^ (-1 - 2 * ρ) := by rw [Real.rpow_one]
          _ = z ^ (1 + (-1 - 2 * ρ)) := (Real.rpow_add hz _ _).symm
          _ = _ := by congr 1; ring
      rw [min_eq_right hz1] at ht
      simp only [fractionalKernel, Set.indicator_of_mem (show z ∈ Ioc (0 : ℝ) 1 from ⟨hz, hz1⟩),
        Set.indicator_of_notMem (show z ∉ Ioi (1 : ℝ) from not_lt.mpr hz1), add_zero]
      calc
        _ ≤ (4 * z * vectorSq f) * z ^ (-1 - 2 * ρ) := ht
        _ = (4 * vectorSq f) * (z * z ^ (-1 - 2 * ρ)) := by ring
        _ = _ := by rw [hpower]
    · rw [min_eq_left (by linarith : 1 ≤ z), mul_one] at ht
      simp only [fractionalKernel,
        Set.indicator_of_notMem (show z ∉ Ioc (0 : ℝ) 1 from fun h => hz1 h.2),
        Set.indicator_of_mem (show z ∈ Ioi (1 : ℝ) from lt_of_not_ge hz1), zero_add]
      exact ht
  · rw [fractionalIntegrand, Set.indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz)]
    exact mul_nonneg (mul_nonneg (by norm_num) (vectorSq_nonneg f)) (fractionalKernel_nonneg ρ z)

/-- Fractional translation energy really is integrable in the claimed range. -/
theorem integrable_fractionalIntegrand {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (σ : Equiv.Perm α) (f : α → ℝ) : Integrable (fractionalIntegrand ρ σ f) := by
  apply ((integrable_fractionalKernel hρ hρhalf).const_mul (4 * vectorSq f)).mono'
    (measurable_fractionalIntegrand ρ σ f).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fractionalIntegrand_nonneg ρ σ f z)]
    exact fractionalIntegrand_le ρ σ f z

def cellFractionalSq (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) : ℝ :=
  ∫ z : ℝ, fractionalIntegrand ρ σ f z

theorem cellFractionalSq_nonneg (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) :
    0 ≤ cellFractionalSq ρ σ f := by
  exact integral_nonneg (fractionalIntegrand_nonneg ρ σ f)

/-- A quantitative fractional inverse estimate in cell units, obtained by
integrating the proved translation estimate. -/
theorem cellFractionalSq_le {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (σ : Equiv.Perm α) (f : α → ℝ) :
    cellFractionalSq ρ σ f ≤
      4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ)) * vectorSq f := by
  calc
    _ ≤ ∫ z : ℝ, (4 * vectorSq f) * fractionalKernel ρ z :=
      integral_mono (integrable_fractionalIntegrand hρ hρhalf σ f)
        ((integrable_fractionalKernel hρ hρhalf).const_mul _) (fractionalIntegrand_le ρ σ f)
    _ = (4 * vectorSq f) * (1 / (1 - 2 * ρ) + 1 / (2 * ρ)) := by
      rw [integral_const_mul, integral_fractionalKernel hρ hρhalf]
    _ = _ := by ring

/-- Squared `L²` energy when a cell has length `density⁻¹`. -/
def stepL2Sq (density : ℝ) (f : α → ℝ) : ℝ := density⁻¹ * vectorSq f

/-- Fractional-cell overlap energy in the original spatial coordinate. -/
def stepTranslationSq (density : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) : ℝ :=
  density⁻¹ * translationSq σ f (density * z)

def stepFractionalSq (density ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) : ℝ :=
  ∫ z : ℝ in Ioi 0, stepTranslationSq density σ f z * z ^ (-1 - 2 * ρ)

theorem stepL2Sq_nonneg {density : ℝ} (hd : 0 < density) (f : α → ℝ) :
    0 ≤ stepL2Sq density f := mul_nonneg (inv_nonneg.mpr hd.le) (vectorSq_nonneg f)

theorem stepTranslationSq_le_min {density z : ℝ} (hd : 0 < density) (hz : 0 ≤ z)
    (σ : Equiv.Perm α) (f : α → ℝ) :
    stepTranslationSq density σ f z ≤ 4 * min 1 (density * z) * stepL2Sq density f := by
  have h := mul_le_mul_of_nonneg_left
    (translationSq_le_min σ f (mul_nonneg hd.le hz)) (inv_nonneg.mpr hd.le)
  simpa only [stepTranslationSq, stepL2Sq, mul_assoc, mul_left_comm, mul_comm] using h

theorem fractional_integrand_rescaling {density z : ℝ} (hd : 0 < density) (hz : 0 < z)
    (ρ : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) :
    stepTranslationSq density σ f z * z ^ (-1 - 2 * ρ) =
      density ^ (2 * ρ) *
        (translationSq σ f (density * z) * (density * z) ^ (-1 - 2 * ρ)) := by
  have hp : density ^ (2 * ρ) * density ^ (-1 - 2 * ρ) = density⁻¹ := by
    rw [← Real.rpow_add hd, show 2 * ρ + (-1 - 2 * ρ) = (-1 : ℝ) by ring,
      Real.rpow_neg_one]
  rw [Real.mul_rpow hd.le hz.le]
  unfold stepTranslationSq
  calc
    _ = (density ^ (2 * ρ) * density ^ (-1 - 2 * ρ)) *
        translationSq σ f (density * z) * z ^ (-1 - 2 * ρ) := by rw [hp]
    _ = _ := by ring

/-- The spatial scaling factor is derived by an actual change of variables
in the improper integral. -/
theorem stepFractionalSq_scaling {density : ℝ} (hd : 0 < density) (ρ : ℝ)
    (σ : Equiv.Perm α) (f : α → ℝ) :
    stepFractionalSq density ρ σ f =
      density ^ (2 * ρ) * density⁻¹ * cellFractionalSq ρ σ f := by
  unfold stepFractionalSq
  calc
    _ = ∫ z : ℝ in Ioi 0, density ^ (2 * ρ) *
        (translationSq σ f (density * z) * (density * z) ^ (-1 - 2 * ρ)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun z hz => fractional_integrand_rescaling hd hz ρ σ f)
    _ = density ^ (2 * ρ) *
        ∫ z : ℝ in Ioi 0, translationSq σ f (density * z) * (density * z) ^ (-1 - 2 * ρ) := by
      rw [integral_const_mul]
    _ = density ^ (2 * ρ) * (density⁻¹ *
        ∫ z : ℝ in Ioi 0, translationSq σ f z * z ^ (-1 - 2 * ρ)) := by
      rw [integral_comp_mul_left_Ioi
        (fun z : ℝ => translationSq σ f z * z ^ (-1 - 2 * ρ)) 0 hd]
      simp only [mul_zero, smul_eq_mul]
    _ = _ := by
      simp only [cellFractionalSq, fractionalIntegrand, integral_indicator measurableSet_Ioi]
      ring

theorem integrable_stepFractional {density ρ : ℝ} (hd : 0 < density)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (σ : Equiv.Perm α) (f : α → ℝ) :
    IntegrableOn (fun z : ℝ => stepTranslationSq density σ f z * z ^ (-1 - 2 * ρ)) (Ioi 0) := by
  have hi : IntegrableOn (fun z : ℝ => translationSq σ f z * z ^ (-1 - 2 * ρ)) (Ioi 0) :=
    (integrable_indicator_iff measurableSet_Ioi).1 (integrable_fractionalIntegrand hρ hρhalf σ f)
  have hscaled : IntegrableOn
      (fun z : ℝ => translationSq σ f (density * z) * (density * z) ^ (-1 - 2 * ρ)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun z : ℝ => translationSq σ f z * z ^ (-1 - 2 * ρ)) 0 hd).2 (by simpa only [mul_zero] using hi)
  exact IntegrableOn.congr_fun (hscaled.const_mul (density ^ (2 * ρ)))
    (fun z hz => (fractional_integrand_rescaling hd hz ρ σ f).symm) measurableSet_Ioi

/-- The fractional inverse estimate at mesh `density⁻¹`, with the expected
`density^(2ρ)` factor and a constant independent of the number of cells. -/
theorem stepFractionalSq_le {density ρ : ℝ} (hd : 0 < density)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (σ : Equiv.Perm α) (f : α → ℝ) :
    stepFractionalSq density ρ σ f ≤
      (4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ))) * density ^ (2 * ρ) * stepL2Sq density f := by
  rw [stepFractionalSq_scaling hd]
  have hh := mul_le_mul_of_nonneg_left (cellFractionalSq_le hρ hρhalf σ f)
    (mul_nonneg (Real.rpow_nonneg hd.le (2 * ρ)) (inv_nonneg.mpr hd.le))
  simpa only [stepL2Sq, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Actual Lebesgue integration of the two overlap pieces of one cell. -/
theorem integral_cell_split {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (A B : ℝ) :
    (∫ u : ℝ in Ioc 0 1, if u ≤ s then A else B) = s * A + (1 - s) * B := by
  have heql : EqOn (fun _ : ℝ => A) (fun u => if u ≤ s then A else B) (Ioc 0 s) := by
    intro u hu
    simp only [ite_eq_left hu.2]
  have heqr : EqOn (fun _ : ℝ => B) (fun u => if u ≤ s then A else B) (Ioc s 1) := by
    intro u hu
    simp only [ite_eq_right (not_le.mpr hu.1)]
  have hl : IntegrableOn (fun u : ℝ => if u ≤ s then A else B) (Ioc 0 s) :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => A) volume 0 s).1.congr_fun
      heql measurableSet_Ioc
  have hr : IntegrableOn (fun u : ℝ => if u ≤ s then A else B) (Ioc s 1) :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume s 1).1.congr_fun
      heqr measurableSet_Ioc
  calc
    _ = (∫ u : ℝ in Ioc 0 s, if u ≤ s then A else B) +
        ∫ u : ℝ in Ioc s 1, if u ≤ s then A else B := by
      rw [← Ioc_union_Ioc_eq_Ioc hs0 hs1]
      exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hl hr
    _ = (∫ _ : ℝ in Ioc 0 s, A) + ∫ _ : ℝ in Ioc s 1, B := by
      congr 1
      · exact setIntegral_congr_fun measurableSet_Ioc heql.symm
      · exact setIntegral_congr_fun measurableSet_Ioc heqr.symm
    _ = _ := by
      rw [← intervalIntegral.integral_of_le hs0, ← intervalIntegral.integral_of_le hs1,
        intervalIntegral.integral_const, intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]

/-- Translation of an actual cellwise constant function on the suspension of
a finite permutation.  For `σ = finRotate N` these are periodic equal cells. -/
def overlapTranslate (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) (x : α) (u : ℝ) : ℝ :=
  if u ≤ 1 - (z - (⌊z⌋₊ : ℝ)) then f ((σ ^ ⌊z⌋₊) x) else f ((σ ^ (⌊z⌋₊ + 1)) x)

/-- The translation square computed with real Lebesgue integrals inside
the cells, before any finite-sum overlap formula is applied. -/
def lebesgueTranslationSq (σ : Equiv.Perm α) (f : α → ℝ) (z : ℝ) : ℝ :=
  ∑ x, ∫ u : ℝ in Ioc 0 1, (overlapTranslate σ f z x u - f x) ^ 2

/-- The finite overlap expression is proved equal to the actual cellwise
Lebesgue `L²` translation energy. -/
theorem lebesgueTranslationSq_eq (σ : Equiv.Perm α) (f : α → ℝ)
    {z : ℝ} (hz : 0 ≤ z) : lebesgueTranslationSq σ f z = translationSq σ f z := by
  have hθ0 : 0 ≤ z - (⌊z⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hz)
  have hθ1 : z - (⌊z⌋₊ : ℝ) < 1 := Nat.self_sub_floor_lt_one z
  have hi (x : α) :
      (∫ u : ℝ in Ioc 0 1, (overlapTranslate σ f z x u - f x) ^ 2) =
        (1 - (z - (⌊z⌋₊ : ℝ))) * (f ((σ ^ ⌊z⌋₊) x) - f x) ^ 2 +
          (z - (⌊z⌋₊ : ℝ)) * (f ((σ ^ (⌊z⌋₊ + 1)) x) - f x) ^ 2 := by
    calc
      _ = ∫ u : ℝ in Ioc 0 1, if u ≤ 1 - (z - (⌊z⌋₊ : ℝ))
          then (f ((σ ^ ⌊z⌋₊) x) - f x) ^ 2 else (f ((σ ^ (⌊z⌋₊ + 1)) x) - f x) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        unfold overlapTranslate
        dsimp only
        split_ifs <;> rfl
      _ = _ := by
        rw [integral_cell_split (by linarith) (by linarith)]
        ring
  unfold lebesgueTranslationSq translationSq shiftSq vectorSq
  simp_rw [hi]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-- A spatial translation estimate for the actual Lebesgue cell model. -/
theorem lebesgueTranslationSq_le_min (σ : Equiv.Perm α) (f : α → ℝ)
    {z : ℝ} (hz : 0 ≤ z) :
    lebesgueTranslationSq σ f z ≤ 4 * min 1 z * vectorSq f := by
  rw [lebesgueTranslationSq_eq σ f hz]
  exact translationSq_le_min σ f hz

/-- Massive positive fractional energy in the equal-cell spatial model. -/
def massiveStepSq (Λ ρ density : ℝ) (σ : Equiv.Perm α) (f : α → ℝ) : ℝ :=
  Λ ^ ρ * stepL2Sq density f + stepFractionalSq density ρ σ f

/-- The full massive step-function inverse inequality in the continuum-cell
Gagliardo model, with the same `(Λ + density²)^ρ` scaling as Section 2. -/
theorem massiveStepSq_inverse {Λ ρ density : ℝ} (hΛ : 0 ≤ Λ) (hd : 0 < density)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (σ : Equiv.Perm α) (f : α → ℝ) :
    massiveStepSq Λ ρ density σ f ≤
      (1 + 4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ))) *
        (Λ + density ^ 2) ^ ρ * stepL2Sq density f := by
  let C := 4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ))
  have hC : 0 ≤ C := by
    have hden : 0 < 1 - 2 * ρ := by linarith
    dsimp [C]
    positivity
  have hE : 0 ≤ stepL2Sq density f := stepL2Sq_nonneg hd f
  have hΛp : Λ ^ ρ ≤ (Λ + density ^ 2) ^ ρ :=
    Real.rpow_le_rpow hΛ (le_add_of_nonneg_right (sq_nonneg density)) hρ.le
  have hdp : density ^ (2 * ρ) ≤ (Λ + density ^ 2) ^ ρ := by
    rw [Real.rpow_mul hd.le, Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg density) (le_add_of_nonneg_left hΛ) hρ.le
  have hfrac := stepFractionalSq_le hd hρ hρhalf σ f
  change Λ ^ ρ * stepL2Sq density f + stepFractionalSq density ρ σ f ≤
    (1 + C) * (Λ + density ^ 2) ^ ρ * stepL2Sq density f
  calc
    _ ≤ Λ ^ ρ * stepL2Sq density f + C * density ^ (2 * ρ) * stepL2Sq density f :=
      add_le_add le_rfl hfrac
    _ ≤ (Λ + density ^ 2) ^ ρ * stepL2Sq density f +
        C * (Λ + density ^ 2) ^ ρ * stepL2Sq density f :=
      add_le_add (mul_le_mul_of_nonneg_right hΛp hE)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdp hC) hE)
    _ = _ := by ring

/-- The model on the periodic dyadic mesh, with its canonical cyclic
successor permutation. -/
theorem dyadic_massiveStepSq_inverse (n : ℕ) (f : Fin (2 ^ n) → ℝ)
    {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    massiveStepSq Λ ρ ((2 : ℝ) ^ n) (finRotate (2 ^ n)) f ≤
      (1 + 4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ))) *
        (Λ + (2 : ℝ) ^ (2 * n)) ^ ρ * stepL2Sq ((2 : ℝ) ^ n) f := by
  have h := massiveStepSq_inverse hΛ (pow_pos (by norm_num : (0 : ℝ) < 2) n)
    hρ hρhalf (finRotate (2 ^ n)) f
  simpa only [← pow_mul, Nat.mul_comm n 2] using h

end CyclicStep

/-! ## The actual circle Fourier representation of translation energy -/

namespace CircleFractional

open MeasureTheory AddCircle

variable {T : ℝ}

theorem fourier_translate (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem fourier_mul_neg (n : ℤ) (x : AddCircle T) :
    fourier n x * fourier (-n) x = 1 := by
  rw [← fourier_add, add_neg_cancel, fourier_zero]

variable [Fact (0 < T)]

/-- Translating an actual circle function multiplies its Fourier coefficient
by the corresponding character. -/
theorem fourierCoeff_translate (f : AddCircle T → ℂ) (y : AddCircle T) (n : ℤ) :
    fourierCoeff (fun x => f (x + y)) n = fourier n y * fourierCoeff f n := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  calc
    _ = ∫ x : AddCircle T, fourier n y *
        (fourier (-n) (x + y) * f (x + y)) ∂haarAddCircle := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      rw [fourier_translate]
      symm
      calc
        _ = (fourier n y * fourier (-n) y) * (fourier (-n) x * f (x + y)) := by ring
        _ = _ := by rw [fourier_mul_neg, one_mul]
    _ = fourier n y *
        ∫ x : AddCircle T, fourier (-n) (x + y) * f (x + y) ∂haarAddCircle := by
      rw [integral_const_mul]
    _ = _ := by
      congr 1
      exact integral_add_right_eq_self (fun x : AddCircle T => fourier (-n) x * f x) y

theorem fourierCoeff_sub (f g : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    (hg : Integrable g haarAddCircle) (n : ℤ) :
    fourierCoeff (fun x => f x - g x) n = fourierCoeff f n - fourierCoeff g n := by
  unfold fourierCoeff
  simp only [smul_sub]
  exact integral_sub (hf.fourier_smul _) (hg.fourier_smul _)

/-- Translation differences retain the exact signed multiplier, including
the vanishing zero Fourier mode. -/
theorem fourierCoeff_translation_difference (f : AddCircle T → ℂ)
    (hf : Integrable f haarAddCircle) (y : AddCircle T) (n : ℤ) :
    fourierCoeff (fun x => f (x + y) - f x) n = (fourier n y - 1) * fourierCoeff f n := by
  rw [fourierCoeff_sub _ _ (hf.comp_add_right y) hf, fourierCoeff_translate]
  ring

/-- Parseval with an ordinary measurable function rather than an `Lp`
representative. -/
theorem hasSum_sq_fourierCoeff_of_memLp (f : AddCircle T → ℂ)
    (hf : MemLp f 2 haarAddCircle) :
    HasSum (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
      (∫ x : AddCircle T, ‖f x‖ ^ 2 ∂haarAddCircle) := by
  have hc : fourierCoeff (hf.toLp f) = fourierCoeff f :=
    fourierCoeff_congr_ae hf.coeFn_toLp
  have hi : (∫ x : AddCircle T, ‖(hf.toLp f) x‖ ^ 2 ∂haarAddCircle) =
      ∫ x : AddCircle T, ‖f x‖ ^ 2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  simpa only [hc, hi] using hasSum_sq_fourierCoeff (hf.toLp f)

/-- Actual circle `L²` translation energy equals the Fourier multiplier
series.  This supplies the spectral side of the Gagliardo bridge. -/
theorem hasSum_translation_energy (f : AddCircle T → ℂ) (hf : MemLp f 2 haarAddCircle)
    (y : AddCircle T) :
    HasSum (fun n : ℤ => ‖fourier n y - 1‖ ^ 2 * ‖fourierCoeff f n‖ ^ 2)
      (∫ x : AddCircle T, ‖f (x + y) - f x‖ ^ 2 ∂haarAddCircle) := by
  have ht : MemLp (fun x => f (x + y)) 2 haarAddCircle :=
    hf.comp_measurePreserving (measurePreserving_add_right haarAddCircle y)
  have hd : MemLp (fun x => f (x + y) - f x) 2 haarAddCircle := ht.sub hf
  have h := hasSum_sq_fourierCoeff_of_memLp _ hd
  have hfi : Integrable f haarAddCircle := hf.integrable (by norm_num)
  simpa only [fourierCoeff_translation_difference f hfi, norm_mul, mul_pow] using h

section UnitCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The scalar character multiplier for one spatial Fourier frequency. -/
def unitAmplitude (z : ℝ) : ℝ := ‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) - 1‖ ^ 2

theorem unitCharacter_exp (z : ℝ) :
    fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) = Complex.exp (Complex.I * (2 * Real.pi * z : ℝ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem continuous_unitAmplitude : Continuous unitAmplitude := by
  unfold unitAmplitude
  fun_prop

theorem unitAmplitude_nonneg (z : ℝ) : 0 ≤ unitAmplitude z := sq_nonneg _

theorem unitAmplitude_le_four (z : ℝ) : unitAmplitude z ≤ 4 := by
  have hn : ‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
  have h : ‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [hn, norm_one]; norm_num
  have hs := (sq_le_sq).2
    (show |‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) - 1‖| ≤ |(2 : ℝ)| by
      simpa only [abs_of_nonneg (norm_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using h)
  norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num] at hs
  exact hs

theorem unitAmplitude_le_quadratic (z : ℝ) :
    unitAmplitude z ≤ (2 * Real.pi) ^ 2 * z ^ 2 := by
  have h : ‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) - 1‖ ≤ |2 * Real.pi * z| := by
    rw [unitCharacter_exp]
    simpa only [Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * z))
  have hs := (sq_le_sq).2
    (show |‖fourier (T := 1) 1 (z : AddCircle (1 : ℝ)) - 1‖| ≤ |2 * Real.pi * z| by
      simpa only [abs_of_nonneg (norm_nonneg _)] using h)
  simpa only [unitAmplitude, mul_pow] using hs

theorem unitAmplitude_le_min {z : ℝ} (hz : 0 ≤ z) :
    unitAmplitude z ≤ (4 + (2 * Real.pi) ^ 2) * min 1 z := by
  by_cases hz1 : z ≤ 1
  · rw [min_eq_right hz1]
    have hsq : z ^ 2 ≤ z := by nlinarith
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg (2 * Real.pi))
    have hquad := unitAmplitude_le_quadratic z
    nlinarith
  · rw [min_eq_left (by linarith : 1 ≤ z), mul_one]
    nlinarith [unitAmplitude_le_four z, sq_nonneg (2 * Real.pi)]

theorem weighted_power_le_fractionalKernel (ρ C e z : ℝ) (hz : 0 < z)
    (he : e ≤ C * min 1 z) :
    e * z ^ (-1 - 2 * ρ) ≤ C * CyclicStep.fractionalKernel ρ z := by
  have ht := mul_le_mul_of_nonneg_right he (Real.rpow_nonneg hz.le (-1 - 2 * ρ))
  by_cases hz1 : z ≤ 1
  · have hpower : z * z ^ (-1 - 2 * ρ) = z ^ (-2 * ρ) := by
      calc
        _ = z ^ (1 : ℝ) * z ^ (-1 - 2 * ρ) := by rw [Real.rpow_one]
        _ = z ^ (1 + (-1 - 2 * ρ)) := (Real.rpow_add hz _ _).symm
        _ = _ := by congr 1; ring
    rw [min_eq_right hz1] at ht
    simp only [CyclicStep.fractionalKernel,
      Set.indicator_of_mem (show z ∈ Set.Ioc (0 : ℝ) 1 from ⟨hz, hz1⟩),
      Set.indicator_of_notMem (show z ∉ Set.Ioi (1 : ℝ) from not_lt.mpr hz1), add_zero]
    simpa only [mul_assoc, hpower] using ht
  · rw [min_eq_left (by linarith : 1 ≤ z), mul_one] at ht
    simpa only [CyclicStep.fractionalKernel,
      Set.indicator_of_notMem (show z ∉ Set.Ioc (0 : ℝ) 1 from fun h => hz1 h.2),
      Set.indicator_of_mem (show z ∈ Set.Ioi (1 : ℝ) from lt_of_not_ge hz1), zero_add] using ht

def unitFractionalIntegrand (ρ : ℝ) (z : ℝ) : ℝ :=
  (Set.Ioi (0 : ℝ)).indicator (fun x => unitAmplitude x * x ^ (-1 - 2 * ρ)) z

theorem unitFractionalIntegrand_nonneg (ρ z : ℝ) : 0 ≤ unitFractionalIntegrand ρ z := by
  exact Set.indicator_nonneg (fun (x : ℝ) hx =>
    mul_nonneg (unitAmplitude_nonneg x) (Real.rpow_nonneg hx.le _)) z

theorem integrable_unitFractionalIntegrand {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Integrable (unitFractionalIntegrand ρ) := by
  have hm : Measurable (unitFractionalIntegrand ρ) := by
    apply Measurable.indicator _ measurableSet_Ioi
    exact continuous_unitAmplitude.measurable.mul (by fun_prop)
  apply ((CyclicStep.integrable_fractionalKernel hρ hρhalf).const_mul
    (4 + (2 * Real.pi) ^ 2)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (unitFractionalIntegrand_nonneg ρ z)]
  by_cases hz : 0 < z
  · rw [unitFractionalIntegrand, Set.indicator_of_mem (show z ∈ Set.Ioi (0 : ℝ) from hz)]
    exact weighted_power_le_fractionalKernel ρ _ _ z hz (unitAmplitude_le_min hz.le)
  · rw [unitFractionalIntegrand,
      Set.indicator_of_notMem (show z ∉ Set.Ioi (0 : ℝ) from hz)]
    exact mul_nonneg (by positivity) (CyclicStep.fractionalKernel_nonneg ρ z)

theorem unitAmplitude_half : unitAmplitude (1 / 2) = 4 := by
  unfold unitAmplitude
  rw [unitCharacter_exp]
  have he : Complex.I * (2 * Real.pi * (1 / 2 : ℝ) : ℝ) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]
  norm_num

def unitFractionalMass (ρ : ℝ) : ℝ := ∫ z : ℝ, unitFractionalIntegrand ρ z

/-- The reference fractional Fourier multiplier has a finite strictly positive
normalizing constant.  Positivity is established on an actual spatial interval. -/
theorem unitFractionalMass_pos {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    0 < unitFractionalMass ρ := by
  have hc : ContinuousOn (unitFractionalIntegrand ρ) (Set.Icc (1 / 4 : ℝ) (3 / 4)) := by
    have hpow : ContinuousOn (fun z : ℝ => z ^ (-1 - 2 * ρ))
        (Set.Icc (1 / 4 : ℝ) (3 / 4)) := by
      apply continuousOn_id.rpow_const
      intro z hz
      left
      exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hz.1).ne'
    apply (continuous_unitAmplitude.continuousOn.mul hpow).congr
    intro z hz
    rw [unitFractionalIntegrand,
      Set.indicator_of_mem (show z ∈ Set.Ioi (0 : ℝ) from
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4) hz.1)]
    rfl
  have hhalf : 0 < unitFractionalIntegrand ρ (1 / 2) := by
    rw [unitFractionalIntegrand,
      Set.indicator_of_mem (show (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num), unitAmplitude_half]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hp : 0 < ∫ z : ℝ in (1 / 4 : ℝ)..(3 / 4 : ℝ), unitFractionalIntegrand ρ z :=
    intervalIntegral.integral_pos (by norm_num) hc
      (fun z _ => unitFractionalIntegrand_nonneg ρ z) ⟨1 / 2, by norm_num, hhalf⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 4 : ℝ) ≤ 3 / 4)] at hp
  exact hp.trans_le (setIntegral_le_integral (integrable_unitFractionalIntegrand hρ hρhalf)
    (ae_of_all _ (unitFractionalIntegrand_nonneg ρ)))

def frequencyAmplitude (n : ℤ) (z : ℝ) : ℝ :=
  ‖fourier (T := 1) n (z : AddCircle (1 : ℝ)) - 1‖ ^ 2

theorem frequencyAmplitude_scale (n : ℤ) (z : ℝ) :
    frequencyAmplitude n z = unitAmplitude ((n : ℝ) * z) := by
  have hc : fourier (T := 1) n (z : AddCircle (1 : ℝ)) =
      fourier (T := 1) 1 (((n : ℝ) * z : ℝ) : AddCircle (1 : ℝ)) := by
    rw [fourier_coe_apply, unitCharacter_exp]
    congr 1
    push_cast
    ring
  unfold frequencyAmplitude unitAmplitude
  rw [hc]

theorem frequencyAmplitude_neg (n : ℤ) (z : ℝ) :
    frequencyAmplitude (-n) z = frequencyAmplitude n z := by
  unfold frequencyAmplitude
  rw [fourier_neg]
  have hc (w : ℂ) : starRingEnd ℂ w - 1 = starRingEnd ℂ (w - 1) := by simp
  rw [hc]
  simp only [Complex.norm_conj]

theorem unitAmplitude_neg (z : ℝ) : unitAmplitude (-z) = unitAmplitude z := by
  have h := frequencyAmplitude_neg 1 z
  simpa only [frequencyAmplitude_scale, Int.cast_neg, Int.cast_one, neg_one_mul, one_mul] using h

theorem frequencyAmplitude_abs (n : ℤ) (z : ℝ) :
    frequencyAmplitude n z = unitAmplitude (|(n : ℝ)| * z) := by
  rw [frequencyAmplitude_scale]
  by_cases hn : 0 ≤ (n : ℝ)
  · rw [abs_of_nonneg hn]
  · rw [abs_of_neg (lt_of_not_ge hn), neg_mul, unitAmplitude_neg]

theorem amplitude_integrand_rescaling {a z : ℝ} (ha : 0 < a) (hz : 0 < z) (ρ v : ℝ) :
    v * z ^ (-1 - 2 * ρ) =
      a ^ (1 + 2 * ρ) * (v * (a * z) ^ (-1 - 2 * ρ)) := by
  have hp : a ^ (1 + 2 * ρ) * a ^ (-1 - 2 * ρ) = 1 := by
    rw [← Real.rpow_add ha, show 1 + 2 * ρ + (-1 - 2 * ρ) = (0 : ℝ) by ring,
      Real.rpow_zero]
  rw [Real.mul_rpow ha.le hz.le]
  calc
    _ = (a ^ (1 + 2 * ρ) * a ^ (-1 - 2 * ρ)) * (v * z ^ (-1 - 2 * ρ)) := by rw [hp, one_mul]
    _ = _ := by ring

/-- Exact homogeneous scaling of the fractional character multiplier. -/
theorem amplitude_fractional_scaling {a : ℝ} (ha : 0 < a) (ρ : ℝ) :
    (∫ z : ℝ in Set.Ioi 0, unitAmplitude (a * z) * z ^ (-1 - 2 * ρ)) =
      a ^ (2 * ρ) * unitFractionalMass ρ := by
  calc
    _ = ∫ z : ℝ in Set.Ioi 0, a ^ (1 + 2 * ρ) *
        (unitAmplitude (a * z) * (a * z) ^ (-1 - 2 * ρ)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun z hz => amplitude_integrand_rescaling ha hz ρ _)
    _ = a ^ (1 + 2 * ρ) * (a⁻¹ *
        ∫ z : ℝ in Set.Ioi 0, unitAmplitude z * z ^ (-1 - 2 * ρ)) := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi
        (fun z : ℝ => unitAmplitude z * z ^ (-1 - 2 * ρ)) 0 ha]
      simp only [mul_zero, smul_eq_mul]
    _ = _ := by
      have hp : a ^ (1 + 2 * ρ) * a⁻¹ = a ^ (2 * ρ) := by
        rw [← Real.rpow_neg_one a, ← Real.rpow_add ha]
        congr 1
        ring
      simp only [unitFractionalMass, unitFractionalIntegrand, integral_indicator measurableSet_Ioi]
      rw [← mul_assoc, hp]

theorem integrable_amplitude_fractional {a ρ : ℝ} (ha : 0 < a)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    IntegrableOn (fun z : ℝ => unitAmplitude (a * z) * z ^ (-1 - 2 * ρ)) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun z : ℝ => unitAmplitude z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0) :=
    (integrable_indicator_iff measurableSet_Ioi).1 (integrable_unitFractionalIntegrand hρ hρhalf)
  have hs : IntegrableOn (fun z : ℝ => unitAmplitude (a * z) * (a * z) ^ (-1 - 2 * ρ)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun z : ℝ => unitAmplitude z * z ^ (-1 - 2 * ρ)) 0 ha).2 (by simpa only [mul_zero] using hi)
  exact IntegrableOn.congr_fun (hs.const_mul (a ^ (1 + 2 * ρ)))
    (fun z hz => (amplitude_integrand_rescaling ha hz ρ _).symm) measurableSet_Ioi

/-- For every nonzero integer mode, the Gagliardo multiplier is exactly
`|n|^(2ρ)` times the common positive constant. -/
theorem frequency_fractional_integral (ρ : ℝ) (n : ℤ) (hn : n ≠ 0) :
    (∫ z : ℝ in Set.Ioi 0, frequencyAmplitude n z * z ^ (-1 - 2 * ρ)) =
      |(n : ℝ)| ^ (2 * ρ) * unitFractionalMass ρ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  simp_rw [frequencyAmplitude_abs]
  exact amplitude_fractional_scaling (abs_pos.mpr hnR) ρ

theorem frequency_fractional_integral_all {ρ : ℝ} (hρ : 0 < ρ) (n : ℤ) :
    (∫ z : ℝ in Set.Ioi 0, frequencyAmplitude n z * z ^ (-1 - 2 * ρ)) =
      |(n : ℝ)| ^ (2 * ρ) * unitFractionalMass ρ := by
  by_cases hn : n = 0
  · subst n
    simp [frequencyAmplitude, Real.zero_rpow (by linarith : 2 * ρ ≠ 0)]
  · exact frequency_fractional_integral ρ n hn

theorem integrable_frequency_fractional {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (n : ℤ) :
    IntegrableOn (fun z : ℝ => frequencyAmplitude n z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simp only [frequencyAmplitude, fourier_zero, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul]
    exact integrableOn_zero
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    simpa only [frequencyAmplitude_abs] using
      integrable_amplitude_fractional (abs_pos.mpr hnR) hρ hρhalf

def circleTranslationEnergy (f : AddCircle (1 : ℝ) → ℂ) (z : ℝ) : ℝ :=
  ∫ x : AddCircle (1 : ℝ), ‖f (x + (z : AddCircle (1 : ℝ))) - f x‖ ^ 2 ∂haarAddCircle

def circleFractionalSq (ρ : ℝ) (f : AddCircle (1 : ℝ) → ℂ) : ℝ :=
  ∫ z : ℝ in Set.Ioi 0, circleTranslationEnergy f z * z ^ (-1 - 2 * ρ)

theorem finite_translation_energy_le (f : AddCircle (1 : ℝ) → ℂ)
    (hf : MemLp f 2 haarAddCircle) (F : Finset ℤ) (z : ℝ) :
    (∑ n ∈ F, frequencyAmplitude n z * ‖fourierCoeff f n‖ ^ 2) ≤ circleTranslationEnergy f z := by
  exact sum_le_hasSum F (fun n _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hasSum_translation_energy f hf (z : AddCircle (1 : ℝ)))

/-- Finite Fourier energy is bounded by actual spatial Gagliardo energy.
Only finite sums are interchanged with integration in this proof. -/
theorem spectral_fractional_finset_le {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0))
    (F : Finset ℤ) :
    unitFractionalMass ρ * (∑ n ∈ F, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) ≤
      circleFractionalSq ρ f := by
  have hi (n : ℤ) : IntegrableOn
      (fun z : ℝ => frequencyAmplitude n z * ‖fourierCoeff f n‖ ^ 2 * z ^ (-1 - 2 * ρ)) (Set.Ioi 0) := by
    have h : IntegrableOn (fun z : ℝ => ‖fourierCoeff f n‖ ^ 2 *
        (frequencyAmplitude n z * z ^ (-1 - 2 * ρ))) (Set.Ioi 0) :=
      (integrable_frequency_fractional hρ hρhalf n).const_mul (‖fourierCoeff f n‖ ^ 2)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have heval (n : ℤ) :
      (∫ z : ℝ in Set.Ioi 0, frequencyAmplitude n z * ‖fourierCoeff f n‖ ^ 2 * z ^ (-1 - 2 * ρ)) =
        unitFractionalMass ρ * (|(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) := by
    calc
      _ = ‖fourierCoeff f n‖ ^ 2 *
          ∫ z : ℝ in Set.Ioi 0, frequencyAmplitude n z * z ^ (-1 - 2 * ρ) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        dsimp only
        ring
      _ = _ := by rw [frequency_fractional_integral_all hρ]; ring
  calc
    _ = ∫ z : ℝ in Set.Ioi 0,
        ∑ n ∈ F, frequencyAmplitude n z * ‖fourierCoeff f n‖ ^ 2 * z ^ (-1 - 2 * ρ) := by
      rw [integral_finsetSum F (fun n _ => hi n)]
      simp_rw [heval]
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply integral_mono_ae (integrable_finsetSum F (fun n _ => hi n)) hG
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have h := mul_le_mul_of_nonneg_right (finite_translation_energy_le f hf F z)
        (Real.rpow_nonneg hz.le (-1 - 2 * ρ))
      simpa only [Finset.sum_mul] using h

theorem spectral_fractional_finset_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0))
    (F : Finset ℤ) :
    (∑ n ∈ F, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) ≤
      (unitFractionalMass ρ)⁻¹ * circleFractionalSq ρ f := by
  have h := spectral_fractional_finset_le hρ hρhalf f hf hG F
  have hm := unitFractionalMass_pos hρ hρhalf
  have hd : (∑ n ∈ F, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) ≤
      circleFractionalSq ρ f / unitFractionalMass ρ :=
    (le_div_iff₀ hm).2 (by simpa only [mul_comm] using h)
  simpa only [div_eq_mul_inv, mul_comm] using hd

/-- The actual fractional Fourier sequence is summable as a consequence
of finite spatial Gagliardo energy. -/
theorem summable_spectral_fractional {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0)) :
    Summable (fun n : ℤ => |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) := by
  exact summable_of_sum_le (fun n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))
    (spectral_fractional_finset_bound hρ hρhalf f hf hG)

/-- A genuine Gagliardo-to-Fourier fractional Sobolev inequality on the
unit circle, including the infinite Fourier sum. -/
theorem spectral_fractional_tsum_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (f : AddCircle (1 : ℝ) → ℂ) (hf : MemLp f 2 haarAddCircle)
    (hG : IntegrableOn (fun z : ℝ => circleTranslationEnergy f z * z ^ (-1 - 2 * ρ)) (Set.Ioi 0)) :
    (∑' n : ℤ, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff f n‖ ^ 2) ≤
      (unitFractionalMass ρ)⁻¹ * circleFractionalSq ρ f := by
  exact Real.tsum_le_of_sum_le
    (fun n => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _))
    (spectral_fractional_finset_bound hρ hρhalf f hf hG)

end UnitCircle

end CircleFractional

/-! ## Literal periodic step functions on the unit circle -/

namespace CircleStep

open Finset MeasureTheory Set AddCircle

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Right-closed equal cells make the overlap formula exact at boundaries. -/
def realStep (N : ℕ) (v : ZMod N → ℝ) (x : ℝ) : ℝ :=
  v (((⌈(N : ℝ) * x⌉ - 1 : ℤ) : ZMod N))

theorem realStep_periodic (N : ℕ) (v : ZMod N → ℝ) : Function.Periodic (realStep N v) 1 := by
  intro x
  unfold realStep
  congr 1
  rw [mul_add, mul_one, Int.ceil_add_natCast]
  push_cast
  simp only [ZMod.natCast_self, add_zero]

def circleStep (N : ℕ) (v : ZMod N → ℝ) (x : AddCircle (1 : ℝ)) : ℂ :=
  ((realStep_periodic N v).lift x : ℝ)

@[simp] theorem circleStep_coe (N : ℕ) (v : ZMod N → ℝ) (x : ℝ) :
    circleStep N v (x : AddCircle (1 : ℝ)) = (realStep N v x : ℂ) := rfl

theorem measurable_realStep (N : ℕ) (v : ZMod N → ℝ) : Measurable (realStep N v) := by
  have hv : Measurable (fun k : ℤ => v (k : ZMod N)) := measurable_of_countable _
  exact hv.comp (((measurable_const.mul measurable_id).ceil).sub_const 1)

theorem circleStep_eq_liftIoc (N : ℕ) (v : ZMod N → ℝ) :
    circleStep N v = AddCircle.liftIoc (1 : ℝ) 0 (fun x => (realStep N v x : ℂ)) := by
  ext x
  let y := AddCircle.equivIoc (1 : ℝ) 0 x
  have hy : ((y : ℝ) : AddCircle (1 : ℝ)) = x := AddCircle.coe_equivIoc
  rw [← hy, circleStep_coe, AddCircle.liftIoc_coe_apply y.property]

theorem circleStep_memLp (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    MemLp (circleStep N v) 2 haarAddCircle := by
  have hm : Measurable (fun x : ℝ => (realStep N v x : ℂ)) := by
    exact Complex.continuous_ofReal.measurable.comp (measurable_realStep N v)
  have hb (x : ℝ) : ‖(realStep N v x : ℂ)‖ ≤ ∑ j : ZMod N, ‖v j‖ := by
    rw [Complex.norm_real]
    exact single_le_sum (fun j _ => norm_nonneg (v j)) (mem_univ _)
  have hi : MemLp (fun x : ℝ => (realStep N v x : ℂ)) 2 (volume.restrict (Ioc 0 1)) := by
    let : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) 1) < ⊤)⟩
    exact MemLp.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hb)
  rw [circleStep_eq_liftIoc]
  have hi' : MemLp (fun x : ℝ => (realStep N v x : ℂ)) 2
      (volume.restrict (Ioc 0 (0 + (1 : ℝ)))) := by simpa only [zero_add] using hi
  exact (hi'.memLp_liftIoc).haarAddCircle

def cyclicSuccessor (N : ℕ) : Equiv.Perm (ZMod N) := Equiv.addRight 1

theorem cyclicSuccessor_pow (N q : ℕ) (j : ZMod N) :
    (cyclicSuccessor N ^ q) j = j + (q : ZMod N) := by
  induction q generalizing j with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp only [cyclicSuccessor, Equiv.coe_addRight, Nat.cast_add, Nat.cast_one]
    ring

/-- Exact evaluation of a translated literal step function inside one cell. -/
theorem realStep_translate_cell (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (j : ZMod N)
    {u z : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (hz : 0 ≤ z) :
    realStep N v (((j.val : ℝ) + u) / N + z) =
      CyclicStep.overlapTranslate (cyclicSuccessor N) v ((N : ℝ) * z) j u := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hθ0 : 0 ≤ (N : ℝ) * z - (⌊(N : ℝ) * z⌋₊ : ℝ) :=
    sub_nonneg.mpr (Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hz))
  have hθ1 : (N : ℝ) * z - (⌊(N : ℝ) * z⌋₊ : ℝ) < 1 :=
    Nat.self_sub_floor_lt_one _
  have hscale : (N : ℝ) * (((j.val : ℝ) + u) / N + z) = j.val + u + (N : ℝ) * z := by
    field_simp
  unfold realStep CyclicStep.overlapTranslate
  rw [hscale]
  split_ifs with hs
  · have hc : ⌈(j.val : ℝ) + u + (N : ℝ) * z⌉ =
        (j.val : ℤ) + (⌊(N : ℝ) * z⌋₊ : ℤ) + 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith [hu.1, hu.2]
    rw [hc, cyclicSuccessor_pow]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring
  · have hc : ⌈(j.val : ℝ) + u + (N : ℝ) * z⌉ =
        (j.val : ℤ) + (⌊(N : ℝ) * z⌋₊ : ℤ) + 2 := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith [hu.1, hu.2]
    rw [hc, cyclicSuccessor_pow]
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring

theorem realStep_cell (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (j : ZMod N)
    {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    realStep N v (((j.val : ℝ) + u) / N) = v j := by
  have h := realStep_translate_cell N v j hu (z := 0) le_rfl
  simpa only [add_zero, mul_zero, CyclicStep.overlapTranslate, Nat.floor_zero,
    Nat.cast_zero, sub_zero, pow_zero, Equiv.Perm.one_apply, ite_eq_left hu.2] using h

theorem interval_cell_integral (N : ℕ) (hN : 0 < N) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume 0 1) :
    (∫ x : ℝ in 0..1, g x) = (N : ℝ)⁻¹ *
      ∑ j ∈ range N, ∫ u : ℝ in 0..1, g (((j : ℝ) + u) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale (j : ℕ) : (∫ u : ℝ in 0..1, g (((j : ℝ) + u) / N)) =
      (N : ℝ) * ∫ x : ℝ in ((j : ℝ) / N)..(((j : ℝ) + 1) / N), g x := by
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => g (x / N)) (j : ℝ),
      intervalIntegral.integral_comp_div g hNR.ne']
    simp only [add_zero, smul_eq_mul]
  have hint (j : ℕ) (hj : j < N) :
      IntervalIntegrable g volume ((j : ℝ) / N) ((j + 1 : ℕ) / (N : ℝ)) := by
    have hJ : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr hj
    have ha0 : (0 : ℝ) ≤ (j : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
    have hab : (j : ℝ) / N ≤ ((j : ℝ) + 1) / N :=
      div_le_div_of_nonneg_right (by linarith) hNR.le
    have hb1 : ((j : ℝ) + 1) / N ≤ 1 := (div_le_one hNR).2 hJ
    simp only [Nat.cast_add, Nat.cast_one]
    apply hg.mono_set
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0 hb1
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ) / N) hint
  simp only [Nat.cast_zero, zero_div, div_self hNR.ne'] at hs
  simp_rw [hscale]
  rw [← mul_sum, ← mul_assoc, inv_mul_cancel₀ hNR.ne', one_mul]
  simpa only [Nat.cast_add, Nat.cast_one] using hs.symm

/-- Decomposition of an actual unit-circle integral into equal Lebesgue cells. -/
theorem circle_cell_integral (N : ℕ) [NeZero N] (g : AddCircle (1 : ℝ) → ℝ)
    (hg : Integrable g haarAddCircle) :
    (∫ x : AddCircle (1 : ℝ), g x ∂haarAddCircle) = (N : ℝ)⁻¹ *
      ∑ j : ZMod N, ∫ u : ℝ in Ioc 0 1, g ((((j.val : ℝ) + u) / N : ℝ) : AddCircle (1 : ℝ)) := by
  have hv : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hgV : Integrable g volume := hv.symm ▸ hg
  have hrealLp : MemLp (fun x : ℝ => g (x : AddCircle (1 : ℝ))) 1
      (volume.restrict (Ioc 0 (0 + (1 : ℝ)))) :=
    (memLp_one_iff_integrable.2 hgV).comp_measurePreserving (AddCircle.measurePreserving_mk 1 0)
  have hrealI : IntegrableOn (fun x : ℝ => g (x : AddCircle (1 : ℝ))) (Ioc 0 1) := by
    change Integrable (fun x : ℝ => g (x : AddCircle (1 : ℝ))) (volume.restrict (Ioc 0 1))
    simpa only [zero_add] using memLp_one_iff_integrable.1 hrealLp
  have hreal : IntervalIntegrable (fun x : ℝ => g (x : AddCircle (1 : ℝ))) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hrealI
  have hi : (∫ x : AddCircle (1 : ℝ), g x ∂haarAddCircle) =
      ∫ x : ℝ in 0..1, g (x : AddCircle (1 : ℝ)) := by
    rw [← hv]
    simpa only [zero_add] using (AddCircle.intervalIntegral_preimage (1 : ℝ) 0 g).symm
  rw [hi, interval_cell_integral N (Nat.pos_of_ne_zero (NeZero.ne N)) _ hreal]
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change _ = ((n + 1 : ℕ) : ℝ)⁻¹ *
      (∑ j : Fin (n + 1), ∫ u : ℝ in Ioc 0 1,
        g ((((j.val : ℝ) + u) / ((n + 1 : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ)))
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ∫ u : ℝ in Ioc 0 1,
      g ((((j : ℝ) + u) / ((n + 1 : ℕ) : ℝ) : ℝ) : AddCircle (1 : ℝ)))]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_of_le zero_le_one]

/-- The literal circle step function has exactly the expected normalized
finite-cell `L²` norm. -/
theorem circleStep_L2 (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    (∫ x : AddCircle (1 : ℝ), ‖circleStep N v x‖ ^ 2 ∂haarAddCircle) =
      CyclicStep.stepL2Sq (N : ℝ) v := by
  rw [circle_cell_integral N _ ((circleStep_memLp N v).integrable_norm_pow (by norm_num))]
  unfold CyclicStep.stepL2Sq FiniteTransport.vectorSq
  congr 1
  apply sum_congr rfl
  intro j hj
  calc
    _ = ∫ _ : ℝ in Ioc 0 1, (v j) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [circleStep_coe, realStep_cell N v j hu, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_const]
      norm_num

/-- Exact identification of the literal circle translation energy with the
proved finite overlap model. -/
theorem circleStep_translationEnergy (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {z : ℝ} (hz : 0 ≤ z) :
    CircleFractional.circleTranslationEnergy (circleStep N v) z =
      CyclicStep.stepTranslationSq (N : ℝ) (cyclicSuccessor N) v z := by
  have hf := circleStep_memLp N v
  have ht : MemLp (fun x : AddCircle (1 : ℝ) => circleStep N v (x + (z : AddCircle (1 : ℝ))))
      2 haarAddCircle := hf.comp_measurePreserving (measurePreserving_add_right haarAddCircle _)
  have hg : Integrable (fun x : AddCircle (1 : ℝ) =>
      ‖circleStep N v (x + (z : AddCircle (1 : ℝ))) - circleStep N v x‖ ^ 2) haarAddCircle := by
    simpa only [Pi.sub_apply] using (ht.sub hf).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  unfold CircleFractional.circleTranslationEnergy
  rw [circle_cell_integral N _ hg]
  unfold CyclicStep.stepTranslationSq
  rw [← CyclicStep.lebesgueTranslationSq_eq (cyclicSuccessor N) v
    (mul_nonneg (Nat.cast_nonneg N) hz)]
  unfold CyclicStep.lebesgueTranslationSq
  congr 1
  apply sum_congr rfl
  intro j hj
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  rw [← AddCircle.coe_add, circleStep_coe, circleStep_coe,
    realStep_translate_cell N v j hu hz, realStep_cell N v j hu]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The actual circle Gagliardo integrand is integrable for every periodic
equal-cell step function, precisely in the subcritical range. -/
theorem integrable_circleStep_fractional (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    IntegrableOn (fun z : ℝ => CircleFractional.circleTranslationEnergy (circleStep N v) z *
      z ^ (-1 - 2 * ρ)) (Ioi 0) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact IntegrableOn.congr_fun (CyclicStep.integrable_stepFractional hN hρ hρhalf (cyclicSuccessor N) v)
    (fun z hz => by rw [circleStep_translationEnergy N v hz.le]) measurableSet_Ioi

theorem circleStep_fractionalSq (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (ρ : ℝ) :
    CircleFractional.circleFractionalSq ρ (circleStep N v) =
      CyclicStep.stepFractionalSq (N : ℝ) ρ (cyclicSuccessor N) v := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  dsimp only
  rw [circleStep_translationEnergy N v hz.le]

/-- Literal periodic step functions satisfy the homogeneous spectral
fractional Sobolev inverse bound.  No identification of a cell model is
left as a hypothesis. -/
theorem circleStep_spectral_inverse (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    (∑' n : ℤ, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff (circleStep N v) n‖ ^ 2) ≤
      (CircleFractional.unitFractionalMass ρ)⁻¹ *
        (4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ))) * (N : ℝ) ^ (2 * ρ) * CyclicStep.stepL2Sq N v := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hp := CircleFractional.unitFractionalMass_pos hρ hρhalf
  calc
    _ ≤ (CircleFractional.unitFractionalMass ρ)⁻¹ *
        CircleFractional.circleFractionalSq ρ (circleStep N v) :=
      CircleFractional.spectral_fractional_tsum_bound hρ hρhalf _ (circleStep_memLp N v)
        (integrable_circleStep_fractional N v hρ hρhalf)
    _ = (CircleFractional.unitFractionalMass ρ)⁻¹ *
        CyclicStep.stepFractionalSq N ρ (cyclicSuccessor N) v := by rw [circleStep_fractionalSq]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (CyclicStep.stepFractionalSq_le hN hρ hρhalf (cyclicSuccessor N) v)
        (inv_nonneg.mpr hp.le)
      simpa only [mul_assoc] using h

def fractionalInverseConstant (ρ : ℝ) : ℝ :=
  (CircleFractional.unitFractionalMass ρ)⁻¹ *
    (4 * (1 / (1 - 2 * ρ) + 1 / (2 * ρ)))

theorem fractionalInverseConstant_nonneg {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    0 ≤ fractionalInverseConstant ρ := by
  have hm := CircleFractional.unitFractionalMass_pos hρ hρhalf
  have hd : 0 < 1 - 2 * ρ := by linarith
  unfold fractionalInverseConstant
  positivity

/-- Fourier massive energy.  `κ = 2π` gives the physical unit-circle
Laplacian eigenvalues; `κ = 1` gives the equivalent normalized convention. -/
def massiveFourierSq (κ Λ ρ : ℝ) (f : AddCircle (1 : ℝ) → ℂ) : ℝ :=
  ∑' n : ℤ, (Λ + (κ * (n : ℝ)) ^ 2) ^ ρ * ‖fourierCoeff f n‖ ^ 2

theorem scaled_frequency_weight_le {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) (n : ℤ) :
    (Λ + (κ * (n : ℝ)) ^ 2) ^ ρ ≤ Λ ^ ρ + κ ^ (2 * ρ) * |(n : ℝ)| ^ (2 * ρ) := by
  calc
    _ ≤ Λ ^ ρ + ((κ * (n : ℝ)) ^ 2) ^ ρ :=
      Real.rpow_add_le_add_rpow hΛ (sq_nonneg _) hρ.le (by linarith)
    _ = _ := by
      rw [Real.rpow_mul hκ 2 ρ, Real.rpow_two,
        Real.rpow_mul (abs_nonneg (n : ℝ)) 2 ρ, Real.rpow_two, sq_abs,
        ← Real.mul_rpow (sq_nonneg κ) (sq_nonneg (n : ℝ))]
      congr 2
      ring

theorem circleStep_massive_finset_inverse (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (F : Finset ℤ) :
    (∑ n ∈ F, (Λ + (κ * (n : ℝ)) ^ 2) ^ ρ * ‖fourierCoeff (circleStep N v) n‖ ^ 2) ≤
      (1 + κ ^ (2 * ρ) * fractionalInverseConstant ρ) * (Λ + (N : ℝ) ^ 2) ^ ρ *
        CyclicStep.stepL2Sq N v := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hE : 0 ≤ CyclicStep.stepL2Sq N v := CyclicStep.stepL2Sq_nonneg hN v
  have hf := circleStep_memLp N v
  have h0 : (∑ n ∈ F, ‖fourierCoeff (circleStep N v) n‖ ^ 2) ≤ CyclicStep.stepL2Sq N v := by
    rw [← circleStep_L2]
    exact sum_le_hasSum F (fun n _ => sq_nonneg _)
      (CircleFractional.hasSum_sq_fourierCoeff_of_memLp _ hf)
  have hH : (∑ n ∈ F, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff (circleStep N v) n‖ ^ 2) ≤
      fractionalInverseConstant ρ * (N : ℝ) ^ (2 * ρ) * CyclicStep.stepL2Sq N v := by
    have hg := integrable_circleStep_fractional N v hρ hρhalf
    have hs := CircleFractional.spectral_fractional_finset_bound hρ hρhalf _ hf hg F
    rw [circleStep_fractionalSq] at hs
    have ht := mul_le_mul_of_nonneg_left
      (CyclicStep.stepFractionalSq_le hN hρ hρhalf (cyclicSuccessor N) v)
      (inv_nonneg.mpr (CircleFractional.unitFractionalMass_pos hρ hρhalf).le)
    exact hs.trans (by simpa only [fractionalInverseConstant, mul_assoc] using ht)
  have hΛp : Λ ^ ρ ≤ (Λ + (N : ℝ) ^ 2) ^ ρ :=
    Real.rpow_le_rpow hΛ (le_add_of_nonneg_right (sq_nonneg _)) hρ.le
  have hNp : (N : ℝ) ^ (2 * ρ) ≤ (Λ + (N : ℝ) ^ 2) ^ ρ := by
    rw [Real.rpow_mul hN.le, Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg _) (le_add_of_nonneg_left hΛ) hρ.le
  have hK : 0 ≤ κ ^ (2 * ρ) := Real.rpow_nonneg hκ _
  have hC := fractionalInverseConstant_nonneg hρ hρhalf
  calc
    _ ≤ ∑ n ∈ F, (Λ ^ ρ + κ ^ (2 * ρ) * |(n : ℝ)| ^ (2 * ρ)) *
        ‖fourierCoeff (circleStep N v) n‖ ^ 2 := by
      apply sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (scaled_frequency_weight_le hκ hΛ hρ hρhalf n) (sq_nonneg _)
    _ = Λ ^ ρ * (∑ n ∈ F, ‖fourierCoeff (circleStep N v) n‖ ^ 2) +
        κ ^ (2 * ρ) * (∑ n ∈ F, |(n : ℝ)| ^ (2 * ρ) * ‖fourierCoeff (circleStep N v) n‖ ^ 2) := by
      simp only [add_mul, sum_add_distrib, mul_assoc, mul_sum]
    _ ≤ Λ ^ ρ * CyclicStep.stepL2Sq N v +
        κ ^ (2 * ρ) * (fractionalInverseConstant ρ * (N : ℝ) ^ (2 * ρ) * CyclicStep.stepL2Sq N v) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (Real.rpow_nonneg hΛ _))
        (mul_le_mul_of_nonneg_left hH hK)
    _ ≤ (Λ + (N : ℝ) ^ 2) ^ ρ * CyclicStep.stepL2Sq N v +
        κ ^ (2 * ρ) * (fractionalInverseConstant ρ * (Λ + (N : ℝ) ^ 2) ^ ρ * CyclicStep.stepL2Sq N v) :=
      add_le_add (mul_le_mul_of_nonneg_right hΛp hE)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNp hC) hE) hK)
    _ = _ := by ring

/-- The massive Fourier energy is finite; finiteness is proved rather than
encoded by an undefined infinite sum. -/
theorem summable_circleStep_massive (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Summable (fun n : ℤ => (Λ + (κ * (n : ℝ)) ^ 2) ^ ρ * ‖fourierCoeff (circleStep N v) n‖ ^ 2) := by
  exact summable_of_sum_le
    (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
    (circleStep_massive_finset_inverse N v hκ hΛ hρ hρhalf)

/-- The full literal step-function massive Sobolev inverse inequality on
the periodic unit interval, with the physical Fourier frequency scale. -/
theorem circleStep_massive_spectral_inverse (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    massiveFourierSq κ Λ ρ (circleStep N v) ≤
      (1 + κ ^ (2 * ρ) * fractionalInverseConstant ρ) * (Λ + (N : ℝ) ^ 2) ^ ρ *
        (∫ x : AddCircle (1 : ℝ), ‖circleStep N v x‖ ^ 2 ∂haarAddCircle) := by
  rw [circleStep_L2]
  exact Real.tsum_le_of_sum_le
    (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))
    (circleStep_massive_finset_inverse N v hκ hΛ hρ hρhalf)

end CircleStep

/-! ## Cholesky coordinates of the constructed finite Haar factor -/

namespace FiniteHaar

open Finset Matrix

/-- Root first, then the two descendant subtrees, with their recursive order.
Disjoint branches may be ordered either way; every ancestor precedes its descendants. -/
abbrev detailLinearOrder : (n : ℕ) → LinearOrder (DetailIndex n)
  | 0 => inferInstanceAs (LinearOrder Empty)
  | n + 1 => by
    let : LinearOrder (DetailIndex n) := detailLinearOrder n
    let e : DetailIndex (n + 1) ≃ Unit ⊕ₗ (DetailIndex n ⊕ₗ DetailIndex n) :=
      (Equiv.sumCongr (Equiv.refl Unit) toLex).trans toLex
    exact LinearOrder.lift' e e.injective

attribute [instance] detailLinearOrder

instance modeLinearOrder (n : ℕ) : LinearOrder (Option (DetailIndex n)) :=
  inferInstanceAs (LinearOrder (WithBot (DetailIndex n)))

instance (priority := 2000) modeLT (n : ℕ) : LT (Option (DetailIndex n)) :=
  (modeLinearOrder n).toLT

/-- Explicitly name the recursive order, avoiding the unrelated disjoint-sum
partial order when a successor index type unfolds. -/
def detailPrecedes (n : ℕ) (i j : DetailIndex n) : Prop :=
  @LT.lt (DetailIndex n) (detailLinearOrder n).toLT i j

theorem detailPrecedes_irrefl (n : ℕ) (i : DetailIndex n) : ¬ detailPrecedes n i i :=
  @lt_irrefl (DetailIndex n) (detailLinearOrder n).toPreorder i

theorem detail_lt_left_iff (n : ℕ) (i j : DetailIndex n) :
    detailPrecedes (n + 1) (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl j)) ↔ detailPrecedes n i j := by
  change (toLex (Sum.inr (toLex (Sum.inl i))) : Unit ⊕ₗ (DetailIndex n ⊕ₗ DetailIndex n)) <
    toLex (Sum.inr (toLex (Sum.inl j))) ↔ detailPrecedes n i j
  rw [Sum.Lex.inr_lt_inr_iff, Sum.Lex.inl_lt_inl_iff]
  rfl

theorem detail_lt_right_iff (n : ℕ) (i j : DetailIndex n) :
    detailPrecedes (n + 1) (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)) ↔ detailPrecedes n i j := by
  change (toLex (Sum.inr (toLex (Sum.inr i))) : Unit ⊕ₗ (DetailIndex n ⊕ₗ DetailIndex n)) <
    toLex (Sum.inr (toLex (Sum.inr j))) ↔ detailPrecedes n i j
  rw [Sum.Lex.inr_lt_inr_iff, Sum.Lex.inr_lt_inr_iff]
  rfl

theorem detail_not_left_lt_root (n : ℕ) (i : DetailIndex n) :
    ¬ detailPrecedes (n + 1) (Sum.inr (Sum.inl i)) (Sum.inl ()) := by
  change ¬ (toLex (Sum.inr (toLex (Sum.inl i))) : Unit ⊕ₗ (DetailIndex n ⊕ₗ DetailIndex n)) <
    toLex (Sum.inl ())
  exact Sum.Lex.not_inr_lt_inl

theorem detail_not_right_lt_root (n : ℕ) (i : DetailIndex n) :
    ¬ detailPrecedes (n + 1) (Sum.inr (Sum.inr i)) (Sum.inl ()) := by
  change ¬ (toLex (Sum.inr (toLex (Sum.inr i))) : Unit ⊕ₗ (DetailIndex n ⊕ₗ DetailIndex n)) <
    toLex (Sum.inl ())
  exact Sum.Lex.not_inr_lt_inl

/-- The mixed ordinary/weighted Haar matrix vanishes above the diagonal. -/
theorem mixed_detail_upper_zero (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i j : DetailIndex n) (hij : detailPrecedes n i j) :
    weightedInner c (detailColumn n (fun _ => 1) i) (detailColumn n c j) = 0 := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at c hc i j ⊢
    have hcl : ∀ x, 0 < c (Sum.inl x) := fun x => hc (Sum.inl x)
    have hcr : ∀ x, 0 < c (Sum.inr x) := fun x => hc (Sum.inr x)
    rcases i with ⟨⟩ | (i | i) <;> rcases j with ⟨⟩ | (j | j)
    · exact (detailPrecedes_irrefl _ _ hij).elim
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_const_left, detailColumn_cancellation n _ hcl,
        weightedInner_zero_right, mul_zero, add_zero]
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_right, weightedInner_const_left,
        detailColumn_cancellation n _ hcr, mul_zero, zero_add]
    · exact (detail_not_left_lt_root n i hij).elim
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, add_zero]
      exact ih _ hcl i j ((detail_lt_left_iff n i j).1 hij)
    · simp only [detailColumn]
      erw [weightedInner_sum]
      simp only [weightedInner_zero_left, weightedInner_zero_right, add_zero]
    · exact (detail_not_right_lt_root n i hij).elim
    · simp only [detailColumn]
      erw [weightedInner_sum]
      simp only [weightedInner_zero_left, weightedInner_zero_right, add_zero]
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, zero_add]
      exact ih _ hcr i j ((detail_lt_right_iff n i j).1 hij)

theorem haarMass_pos {l r : ℝ} (hl : 0 < l) (hr : 0 < r) : 0 < haarMass l r := by
  unfold haarMass
  apply Real.sqrt_pos.2
  positivity

theorem haarLeft_pos {l r : ℝ} (hl : 0 < l) (hr : 0 < r) : 0 < haarLeft l r :=
  div_pos (haarMass_pos hl hr) hl

theorem haarRight_neg {l r : ℝ} (hl : 0 < l) (hr : 0 < r) : haarRight l r < 0 :=
  div_neg_of_neg_of_pos (neg_neg_of_pos (haarMass_pos hl hr)) hr

/-- Ordinary and weighted Haar columns at the same node have positive
weighted pairing, including every depth of the tree. -/
theorem mixed_detail_diag_pos (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : DetailIndex n) :
    0 < weightedInner c (detailColumn n (fun _ => 1) i) (detailColumn n c i) := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at c hc i ⊢
    have hcl : ∀ x, 0 < c (Sum.inl x) := fun x => hc (Sum.inl x)
    have hcr : ∀ x, 0 < c (Sum.inr x) := fun x => hc (Sum.inr x)
    rcases i with ⟨⟩ | (i | i)
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_const_const, weightedInner_const_const]
      have h0 : 0 < totalMass n (fun _ => 1) := totalMass_pos n _ (fun _ => zero_lt_one)
      have hl := totalMass_pos n _ hcl
      have hr := totalMass_pos n _ hcr
      have hp := add_pos
        (mul_pos hl (mul_pos (haarLeft_pos h0 h0) (haarLeft_pos hl hr)))
        (mul_pos hr (mul_pos_of_neg_of_neg (haarRight_neg h0 h0) (haarRight_neg hl hr)))
      simpa only [totalMass] using hp
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, add_zero]
      exact ih _ hcl i
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, zero_add]
      exact ih _ hcr i

/-- The local factor expressed in the fixed ordinary Haar coordinates. -/
def referenceFactor (n : ℕ) (c : Grid n → ℝ) :
    Matrix (Option (DetailIndex n)) (Option (DetailIndex n)) ℝ :=
  (haarMatrix n (fun _ => 1))ᵀ * localFactor n c

theorem referenceFactor_apply (n : ℕ) (c : Grid n → ℝ)
    (i j : Option (DetailIndex n)) :
    referenceFactor n c i j = weightedInner c (haarColumn n (fun _ => 1) i) (haarColumn n c j) := by
  unfold referenceFactor
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, haarMatrix, localFactor_apply, weightedInner]
  apply sum_congr rfl
  intro x hx
  ring

/-- The explicit weighted Haar factor is lower triangular in the fixed
coarse-before-descendant reference order. -/
theorem referenceFactor_lower (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x) :
    (referenceFactor n c).IsLowerTriangular := by
  intro i j hij
  rw [referenceFactor_apply]
  cases i with
  | none =>
    cases j with
    | none =>
      change (⊥ : WithBot (DetailIndex n)) < ⊥ at hij
      exact (WithBot.not_lt_bot _ hij).elim
    | some j =>
      simp only [haarColumn]
      rw [weightedInner_const_left, detailColumn_cancellation n c hc j, mul_zero]
  | some i =>
    cases j with
    | none =>
      change (i : WithBot (DetailIndex n)) < ⊥ at hij
      exact (WithBot.not_lt_bot _ hij).elim
    | some j =>
      have hij' : detailPrecedes n i j := (WithBot.coe_lt_coe).1 hij
      exact mixed_detail_upper_zero n c hc i j hij'

/-- Every Cholesky diagonal entry of the constructed factor is positive. -/
theorem referenceFactor_diag_pos (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : Option (DetailIndex n)) : 0 < referenceFactor n c i i := by
  rw [referenceFactor_apply]
  cases i with
  | none =>
    simp only [haarColumn, weightedInner_const_const]
    have h0 := totalMass_pos n (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
    have hm := totalMass_pos n c hc
    exact mul_pos hm (mul_pos (inv_pos.2 (Real.sqrt_pos.2 h0)) (inv_pos.2 (Real.sqrt_pos.2 hm)))
  | some i => exact mixed_detail_diag_pos n c hc i

theorem referenceFactor_covariance (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x) :
    referenceFactor n c * (referenceFactor n c)ᵀ =
      (haarMatrix n (fun _ => 1))ᵀ * Matrix.diagonal c * haarMatrix n (fun _ => 1) := by
  unfold referenceFactor
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (localFactor n c), localFactor_covariance n c hc, ← Matrix.mul_assoc]

open FiniteTransport

theorem localFactor_one (n : ℕ) :
    localFactor n (fun _ => 1) = haarMatrix n (fun _ => 1) := by
  ext x k
  simp only [localFactor_apply, haarMatrix, one_mul]

theorem referenceHaar_orthogonal (n : ℕ) :
    (haarMatrix n (fun _ => 1))ᵀ * haarMatrix n (fun _ => 1) = 1 := by
  simpa only [localFactor_one] using
    haarMatrix_transpose_mul_localFactor n (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)

theorem referenceHaar_coorthogonal (n : ℕ) :
    haarMatrix n (fun _ => 1) * (haarMatrix n (fun _ => 1))ᵀ = 1 := by
  simpa only [localFactor_one] using
    localFactor_mul_haarMatrix_transpose n (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)

theorem referenceHaar_vectorSq (n : ℕ) (x : Option (DetailIndex n) → ℝ) :
    vectorSq (haarMatrix n (fun _ => 1) *ᵥ x) = vectorSq x := by
  have h := covariance_energy (haarMatrix n (fun _ => 1))ᵀ x
  rw [Matrix.transpose_transpose, referenceHaar_orthogonal, Matrix.one_mulVec] at h
  simpa only [vectorSq, dotProduct, pow_two] using h

theorem referenceHaar_transpose_vectorSq (n : ℕ) (x : Grid n → ℝ) :
    vectorSq ((haarMatrix n (fun _ => 1))ᵀ *ᵥ x) = vectorSq x := by
  have h := covariance_energy (haarMatrix n (fun _ => 1)) x
  rw [referenceHaar_coorthogonal, Matrix.one_mulVec] at h
  simpa only [vectorSq, dotProduct, pow_two] using h

theorem referenceFactor_covariance_energy (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (x : Option (DetailIndex n) → ℝ) :
    x ⬝ᵥ ((referenceFactor n c * (referenceFactor n c)ᵀ) *ᵥ x) =
      ∑ y, c y * ((haarMatrix n (fun _ => 1) *ᵥ x) y) ^ 2 := by
  rw [referenceFactor_covariance n c hc]
  calc
    _ = x ⬝ᵥ ((haarMatrix n (fun _ => 1))ᵀ *ᵥ
        (Matrix.diagonal c *ᵥ (haarMatrix n (fun _ => 1) *ᵥ x))) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = (Matrix.diagonal c *ᵥ (haarMatrix n (fun _ => 1) *ᵥ x)) ⬝ᵥ
        (haarMatrix n (fun _ => 1) *ᵥ x) :=
      Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by
      simp only [dotProduct, Matrix.mulVec_diagonal]
      apply sum_congr rfl
      intro y hy
      ring

theorem referenceFactor_covariance_upper (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (U : ℝ) (hU : ∀ x, c x ≤ U) (x : Option (DetailIndex n) → ℝ) :
    x ⬝ᵥ ((referenceFactor n c * (referenceFactor n c)ᵀ) *ᵥ x) ≤ U * vectorSq x := by
  rw [referenceFactor_covariance_energy n c hc]
  calc
    _ ≤ ∑ y, U * ((haarMatrix n (fun _ => 1) *ᵥ x) y) ^ 2 :=
      sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hU y) (sq_nonneg _)
    _ = U * vectorSq (haarMatrix n (fun _ => 1) *ᵥ x) := by rw [vectorSq, mul_sum]
    _ = _ := by rw [referenceHaar_vectorSq]

theorem referenceFactor_covariance_lower (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (m : ℝ) (hm : ∀ x, m ≤ c x) (x : Option (DetailIndex n) → ℝ) :
    m * vectorSq x ≤ x ⬝ᵥ ((referenceFactor n c * (referenceFactor n c)ᵀ) *ᵥ x) := by
  rw [referenceFactor_covariance_energy n c hc]
  calc
    _ = m * vectorSq (haarMatrix n (fun _ => 1) *ᵥ x) := by rw [referenceHaar_vectorSq]
    _ = ∑ y, m * ((haarMatrix n (fun _ => 1) *ᵥ x) y) ^ 2 := by rw [vectorSq, mul_sum]
    _ ≤ _ := sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hm y) (sq_nonneg _)

theorem frobeniusSq_mul_of_vector_isometry {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (A : Matrix α β ℝ) (B : Matrix β γ ℝ)
    (hA : ∀ x : β → ℝ, vectorSq (A *ᵥ x) = vectorSq x) :
    frobeniusSq (A * B) = frobeniusSq B := by
  calc
    _ = ∑ j, vectorSq (A *ᵥ (fun i => B i j)) := by
      simp only [frobeniusSq, vectorSq, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      exact sum_comm
    _ = ∑ j, vectorSq (fun i => B i j) := by simp_rw [hA]
    _ = _ := by
      simp only [vectorSq, frobeniusSq]
      exact sum_comm

theorem frobeniusSq_mul_transpose_of_vector_isometry {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (A : Matrix α β ℝ) (B : Matrix γ β ℝ)
    (hB : ∀ x : β → ℝ, vectorSq (B *ᵥ x) = vectorSq x) :
    frobeniusSq (A * Bᵀ) = frobeniusSq A := by
  rw [← frobeniusSq_transpose (A * Bᵀ), Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [frobeniusSq_transpose] using frobeniusSq_mul_of_vector_isometry B Aᵀ hB

theorem frobeniusSq_diagonal {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℝ) :
    frobeniusSq (Matrix.diagonal f) = ∑ x, (f x) ^ 2 := by
  simp [frobeniusSq, Matrix.diagonal_apply]

/-- Unitary Haar coordinate changes preserve the signed covariance's
Frobenius norm exactly. -/
theorem referenceCompression_frobeniusSq (n : ℕ) (f : Grid n → ℝ) :
    frobeniusSq ((haarMatrix n (fun _ => 1))ᵀ * Matrix.diagonal f * haarMatrix n (fun _ => 1)) =
      ∑ x, (f x) ^ 2 := by
  rw [Matrix.mul_assoc, frobeniusSq_mul_of_vector_isometry _ _ (referenceHaar_transpose_vectorSq n)]
  have h := frobeniusSq_mul_transpose_of_vector_isometry (Matrix.diagonal f)
    (haarMatrix n (fun _ => 1))ᵀ (referenceHaar_transpose_vectorSq n)
  simp only [Matrix.transpose_transpose] at h
  rw [h, frobeniusSq_diagonal]

theorem referenceFactor_covariance_difference (n : ℕ) (c d : Grid n → ℝ)
    (hc : ∀ x, 0 < c x) (hd : ∀ x, 0 < d x) :
    referenceFactor n c * (referenceFactor n c)ᵀ - referenceFactor n d * (referenceFactor n d)ᵀ =
      (haarMatrix n (fun _ => 1))ᵀ * Matrix.diagonal (c - d) * haarMatrix n (fun _ => 1) := by
  rw [referenceFactor_covariance n c hc, referenceFactor_covariance n d hd,
    ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  rfl

/-- The signed dimension-independent Frobenius estimate now applies to
the actual explicitly constructed weighted Haar factors in reference Haar
coordinates.  Triangularity, positive diagonal, covariance factorization,
ellipticity, and the exact signed right-hand side are all proved above. -/
theorem referenceFactor_signed_frobeniusSq (n : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    frobeniusSq (referenceFactor n c - referenceFactor n d) ≤
      U / m ^ 2 * ∑ x, (c x - d x) ^ 2 := by
  have hcp : ∀ x, 0 < c x := fun x => hm.trans_le (hc x).1
  have hdp : ∀ x, 0 < d x := fun x => hm.trans_le (hd x).1
  have hU : 0 ≤ U := hm.le.trans ((hc (firstLeaf n)).1.trans (hc (firstLeaf n)).2)
  have h := cholesky_signed_frobeniusSq_of_covariance
    (referenceFactor n c) (referenceFactor n d) m U hm hU
    (referenceFactor_lower n c hcp) (referenceFactor_lower n d hdp)
    (referenceFactor_diag_pos n c hcp) (referenceFactor_diag_pos n d hdp)
    (referenceFactor_covariance_upper n c hcp U (fun x => (hc x).2))
    (referenceFactor_covariance_lower n c hcp m (fun x => (hc x).1))
    (referenceFactor_covariance_lower n d hdp m (fun x => (hd x).1))
  rw [referenceFactor_covariance_difference n c d hcp hdp, referenceCompression_frobeniusSq] at h
  exact h

end FiniteHaar
/-! The actual heat semigroup and cancellation under a spatial translation. -/
namespace CircleHeat

open MeasureTheory AddCircle
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
abbrev CircleL2 := Lp ℂ 2 (haarAddCircle (T := (1 : ℝ)))
abbrev FourierL2 := lp (fun _ : ℤ => ℂ) 2

def diagonalLinear (a : ℤ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) : FourierL2 →ₗ[ℂ] FourierL2 where
  toFun f := ⟨fun n => a n * f n, (lp.memℓp f).mono' (fun n => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha n))⟩
  map_add' f g := by apply lp.ext; funext n; exact mul_add _ _ _
  map_smul' c f := by
    apply lp.ext
    funext n
    change a n * (c * f n) = c * (a n * f n)
    ring

theorem diagonalLinear_norm_le (a : ℤ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (f : FourierL2) :
    ‖diagonalLinear a ha f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  change ‖a n * f n‖ ≤ ‖f n‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha n)

def diagonal (a : ℤ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) : FourierL2 →L[ℂ] FourierL2 :=
  (diagonalLinear a ha).mkContinuous 1 (fun f => by simpa using diagonalLinear_norm_le a ha f)

def heatWeight (t : ℝ) (n : ℤ) : ℂ :=
  (Real.exp (-max t 0 * (2 * Real.pi * (n : ℝ)) ^ 2) : ℂ)

theorem heatWeight_norm_le (t : ℝ) (n : ℤ) : ‖heatWeight t n‖ ≤ 1 := by
  rw [heatWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_max_right _ _)) (sq_nonneg _)

/-- The heat semigroup on the literal unit circle, transported through its
complete Fourier Hilbert basis. Its generator has eigenvalues `(2πn)²`. -/
def heat (t : ℝ) : CircleL2 →L[ℂ] CircleL2 :=
  fourierBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    diagonal (heatWeight t) (heatWeight_norm_le t) ∘L
    fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap

theorem heat_fourierCoeff (t : ℝ) (f : CircleL2) (n : ℤ) :
    fourierCoeff (heat t f) n = heatWeight t n * fourierCoeff f n := by
  rw [← fourierBasis_repr]
  change fourierBasis.repr (fourierBasis.repr.symm _) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change heatWeight t n * fourierBasis.repr f n = _
  rw [fourierBasis_repr]

theorem heat_contraction (t : ℝ) (f : CircleL2) : ‖heat t f‖ ≤ ‖f‖ := by
  change ‖fourierBasis.repr.symm
    (diagonal (heatWeight t) (heatWeight_norm_le t) (fourierBasis.repr f))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact (diagonalLinear_norm_le (heatWeight t) (heatWeight_norm_le t)
    (fourierBasis.repr f)).trans_eq (fourierBasis.repr.norm_map f)

theorem heat_zero : heat 0 = ContinuousLinearMap.id ℂ CircleL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  rw [fourierBasis_repr, heat_fourierCoeff]
  simp [heatWeight, fourierBasis_repr]

theorem heat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heat (s + t) = (heat s).comp (heat t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr, ContinuousLinearMap.comp_apply, heat_fourierCoeff]
  have hst : 0 ≤ s + t := add_nonneg hs ht
  simp only [heatWeight, max_eq_left hs, max_eq_left ht, max_eq_left hst]
  rw [show -(s + t) * (2 * Real.pi * (n : ℝ)) ^ 2 =
      -s * (2 * Real.pi * (n : ℝ)) ^ 2 + -t * (2 * Real.pi * (n : ℝ)) ^ 2 by ring,
    Real.exp_add, Complex.ofReal_mul, mul_assoc]

def translate (h : ℝ) (f : CircleL2) : CircleL2 :=
  Lp.compMeasurePreserving (fun x : AddCircle (1 : ℝ) => x + (h : AddCircle (1 : ℝ)))
    (measurePreserving_add_right _ _) f

theorem translate_norm (h : ℝ) (f : CircleL2) : ‖translate h f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

theorem translate_fourierCoeff (h : ℝ) (f : CircleL2) (n : ℤ) :
    fourierCoeff (translate h f) n = fourier n (h : AddCircle (1 : ℝ)) * fourierCoeff f n := by
  unfold translate
  rw [fourierCoeff_congr_ae (Lp.coeFn_compMeasurePreserving _ _)]
  exact CircleFractional.fourierCoeff_translate f _ n

theorem difference_fourierCoeff (h : ℝ) (f : CircleL2) (n : ℤ) :
    fourierCoeff (f - translate h f) n =
      (1 - fourier n (h : AddCircle (1 : ℝ))) * fourierCoeff f n := by
  rw [← fourierBasis_repr, map_sub]
  simp only [lp.coeFn_sub, Pi.sub_apply, fourierBasis_repr, translate_fourierCoeff]
  ring

theorem lp_norm_sq (f : FourierL2) : ‖f‖ ^ 2 = ∑' n : ℤ, ‖f n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f)

theorem norm_sq_fourier (f : CircleL2) : ‖f‖ ^ 2 = ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 := by
  rw [← fourierBasis.repr.norm_map f, lp_norm_sq]
  simp only [fourierBasis_repr]

theorem summable_fourier_sq (f : CircleL2) : Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr] using
    (lp.memℓp (fourierBasis.repr f)).summable (by norm_num)

theorem heatWeight_norm_sq {t : ℝ} (ht : 0 ≤ t) (n : ℤ) :
    ‖heatWeight t n‖ ^ 2 = Real.exp (-(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2) := by
  rw [heatWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    max_eq_left ht, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem heat_translation_multiplier {t : ℝ} (ht : 0 < t) (h : ℝ) (n : ℤ) :
    ‖heatWeight t n * (1 - fourier n (h : AddCircle (1 : ℝ)))‖ ^ 2 ≤ h ^ 2 / (2 * t) := by
  rw [norm_mul, mul_pow, heatWeight_norm_sq ht.le, norm_sub_rev]
  have ha := CircleFractional.unitAmplitude_le_quadratic ((n : ℝ) * h)
  rw [← CircleFractional.frequencyAmplitude_scale] at ha
  have he := (Real.mul_exp_neg_le_exp_neg_one
    (2 * t * (2 * Real.pi * (n : ℝ)) ^ 2)).trans
      (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
  have hmul := mul_le_mul_of_nonneg_left ha
    (Real.exp_nonneg (-(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2))
  change Real.exp (-(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2) *
    CircleFractional.frequencyAmplitude n h ≤ _
  apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
  have heq : -(2 * t * (2 * Real.pi * (n : ℝ)) ^ 2) =
      -(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2 := by ring
  rw [heq] at he
  calc
    _ ≤ (Real.exp (-(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2) *
        ((2 * Real.pi) ^ 2 * ((n : ℝ) * h) ^ 2)) * (2 * t) :=
      mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = h ^ 2 * ((2 * t * (2 * Real.pi * (n : ℝ)) ^ 2) *
        Real.exp (-(2 * t) * (2 * Real.pi * (n : ℝ)) ^ 2)) := by ring
    _ ≤ h ^ 2 * 1 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ = _ := mul_one _

/-- Cancellation gains one spatial scale for the actual heat operator.
This is a genuine `L²` estimate on the circle and uses no assumed smoothing
or dyadic transport estimate. -/
theorem heat_translation_difference_sq {t : ℝ} (ht : 0 < t) (h : ℝ) (f : CircleL2) :
    ‖heat t (f - translate h f)‖ ^ 2 ≤ h ^ 2 / (2 * t) * ‖f‖ ^ 2 := by
  rw [norm_sq_fourier, norm_sq_fourier, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_fourier_sq (heat t (f - translate h f)))
    ((summable_fourier_sq f).mul_left _)
  intro n
  rw [heat_fourierCoeff, difference_fourierCoeff, ← mul_assoc, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (heat_translation_multiplier ht h n) (sq_nonneg _)

def stepLp (N : ℕ) [NeZero N] (v : ZMod N → ℝ) : CircleL2 :=
  (CircleStep.circleStep_memLp N v).toLp (CircleStep.circleStep N v)

theorem stepLp_ae (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    stepLp N v =ᵐ[haarAddCircle] CircleStep.circleStep N v := MemLp.coeFn_toLp _

theorem stepLp_norm_sq (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    ‖stepLp N v‖ ^ 2 = (N : ℝ)⁻¹ * ∑ j, (v j) ^ 2 := by
  rw [norm_sq_fourier, tsum_sq_fourierCoeff]
  calc
    _ = ∫ x : AddCircle (1 : ℝ), ‖CircleStep.circleStep N v x‖ ^ 2 ∂haarAddCircle :=
      integral_congr_ae ((stepLp_ae N v).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
    _ = _ := CircleStep.circleStep_L2 N v

theorem realStep_translate_cellwidth (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (x : ℝ) :
    CircleStep.realStep N v (x + (N : ℝ)⁻¹) =
      CircleStep.realStep N (fun j => v (j + 1)) x := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold CircleStep.realStep
  rw [mul_add, mul_inv_cancel₀ hN, Int.ceil_add_one]
  congr 1
  push_cast
  ring

theorem circleStep_translate_cellwidth (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    (x : AddCircle (1 : ℝ)) :
    CircleStep.circleStep N v (x + ((N : ℝ)⁻¹ : ℝ)) =
      CircleStep.circleStep N (fun j => v (j + 1)) x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (CircleStep.realStep N v (y + (N : ℝ)⁻¹) : ℂ) = _
  rw [realStep_translate_cellwidth]
  rfl

theorem translate_stepLp_cellwidth (N : ℕ) [NeZero N] (v : ZMod N → ℝ) :
    translate (N : ℝ)⁻¹ (stepLp N v) = stepLp N (fun j => v (j + 1)) := by
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving (stepLp N v)
    (measurePreserving_add_right (haarAddCircle (T := (1 : ℝ))) (((N : ℝ)⁻¹ : ℝ) : AddCircle (1 : ℝ)))
  have hshift := (measurePreserving_add_right (haarAddCircle (T := (1 : ℝ)))
    (((N : ℝ)⁻¹ : ℝ) : AddCircle (1 : ℝ))).quasiMeasurePreserving.ae_eq_comp (stepLp_ae N v)
  apply h.trans
  apply hshift.trans
  have hpoint : (CircleStep.circleStep N v ∘
      (fun x : AddCircle (1 : ℝ) => x + (((N : ℝ)⁻¹ : ℝ) : AddCircle (1 : ℝ)))) =ᵐ[haarAddCircle]
      CircleStep.circleStep N (fun j => v (j + 1)) :=
    ae_of_all _ (fun x => circleStep_translate_cellwidth N v x)
  exact hpoint.trans (stepLp_ae N (fun j => v (j + 1))).symm

theorem stepLp_sub (N : ℕ) [NeZero N] (v w : ZMod N → ℝ) :
    stepLp N (fun j => v j - w j) = stepLp N v - stepLp N w := by
  apply Lp.ext
  filter_upwards [stepLp_ae N (fun j => v j - w j), stepLp_ae N v,
    stepLp_ae N w, Lp.coeFn_sub (stepLp N v) (stepLp N w)] with x hd hv hw hs
  rw [hd, hs]
  simp only [Pi.sub_apply, hv, hw]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ((v _ - w _ : ℝ) : ℂ) = (v _ : ℂ) - (w _ : ℂ)
  exact Complex.ofReal_sub _ _

def cellDifference (N : ℕ) (w : ZMod N → ℝ) : ZMod N → ℝ :=
  fun j => w (j + 1) - w j

theorem stepLp_cellDifference (N : ℕ) [NeZero N] (w : ZMod N → ℝ) :
    stepLp N (cellDifference N w) =
      translate (N : ℝ)⁻¹ (stepLp N w) - stepLp N w := by
  rw [translate_stepLp_cellwidth, ← stepLp_sub]
  rfl

theorem cellDifference_norm_sq (N : ℕ) [NeZero N] (w : ZMod N → ℝ)
    (hdisj : ∀ j, w (j + 1) * w j = 0) :
    ‖stepLp N (cellDifference N w)‖ ^ 2 = 2 * ‖stepLp N w‖ ^ 2 := by
  rw [stepLp_norm_sq, stepLp_norm_sq]
  have heach (j : ZMod N) : (cellDifference N w j) ^ 2 = (w (j + 1)) ^ 2 + (w j) ^ 2 := by
    dsimp only [cellDifference]
    nlinarith [hdisj j]
  simp_rw [heach]
  rw [Finset.sum_add_distrib]
  have hperm : (∑ j : ZMod N, (w (j + 1)) ^ 2) = ∑ j : ZMod N, (w j) ^ 2 :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun j => (w j) ^ 2)
  rw [hperm]
  ring

/-- The exact cancellation estimate on equal-cell detail fields. The only
support hypothesis says the generating half-cell fields are disjoint after
one cell shift; the following dyadic construction proves it explicitly. -/
theorem heat_cellDifference_sq {t : ℝ} (ht : 0 < t) (N : ℕ) [NeZero N]
    (w : ZMod N → ℝ) (hdisj : ∀ j, w (j + 1) * w j = 0) :
    ‖heat t (stepLp N (cellDifference N w))‖ ^ 2 ≤
      min 1 ((N : ℝ)⁻¹ ^ 2 / (4 * t)) * ‖stepLp N (cellDifference N w)‖ ^ 2 := by
  rw [min_mul_of_nonneg _ _ (sq_nonneg _)]
  apply le_min
  · simpa using pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t (stepLp N (cellDifference N w))) 2
  · have hd := heat_translation_difference_sq ht (N : ℝ)⁻¹ (stepLp N w)
    have hneg : stepLp N (cellDifference N w) =
        -(stepLp N w - translate (N : ℝ)⁻¹ (stepLp N w)) := by
      rw [stepLp_cellDifference]
      abel
    rw [hneg, map_neg, norm_neg] at ⊢
    simp only [norm_neg]
    have hnorm := cellDifference_norm_sq N w hdisj
    rw [hneg, norm_neg] at hnorm
    calc
      _ ≤ (N : ℝ)⁻¹ ^ 2 / (2 * t) * ‖stepLp N w‖ ^ 2 := hd
      _ = (N : ℝ)⁻¹ ^ 2 / (4 * t) *
          ‖stepLp N w - translate (N : ℝ)⁻¹ (stepLp N w)‖ ^ 2 := by
        rw [hnorm]
        field_simp
        ring

/-- The right halves of each pair of equal cells, with arbitrary amplitudes. -/
def rightHalfVector (N : ℕ) (a : ZMod N → ℝ) (j : ZMod (2 * N)) : ℝ :=
  if j.val % 2 = 1 then a ((j.val / 2 : ℕ) : ZMod N) else 0

theorem successor_parity (N : ℕ) [NeZero N] (j : ZMod (2 * N)) :
    (j + 1).val % 2 ≠ j.val % 2 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have htwo : 2 * N ≠ 1 := by omega
  have hj : j.val < 2 * N := ZMod.val_lt j
  rw [ZMod.val_add, ZMod.val_one'' htwo]
  by_cases hjlt : j.val + 1 < 2 * N
  · rw [Nat.mod_eq_of_lt hjlt]
    omega
  · have heq : j.val + 1 = 2 * N := by omega
    rw [heq, Nat.mod_self]
    omega

theorem rightHalfVector_disjoint (N : ℕ) [NeZero N] (a : ZMod N → ℝ)
    (j : ZMod (2 * N)) :
    rightHalfVector N a (j + 1) * rightHalfVector N a j = 0 := by
  unfold rightHalfVector
  have hp := successor_parity N j
  split_ifs <;> simp_all

/-- Literal ordinary Haar detail on the equal-cell circle: it has value
`a j` on the left child and `-a j` on the right child of parent cell `j`. -/
def dyadicDetailVector (N : ℕ) (a : ZMod N → ℝ) : ZMod (2 * N) → ℝ :=
  cellDifference (2 * N) (rightHalfVector N a)

theorem rightHalfVector_even (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (j : ZMod N) :
    rightHalfVector N a ((2 * j.val : ℕ) : ZMod (2 * N)) = 0 := by
  have hj := ZMod.val_lt j
  have hlt : 2 * j.val < 2 * N := by omega
  rw [rightHalfVector, ZMod.val_natCast_of_lt hlt]
  have heven : (2 * j.val) % 2 ≠ 1 := by omega
  exact ite_eq_right heven

theorem rightHalfVector_odd (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (j : ZMod N) :
    rightHalfVector N a ((2 * j.val + 1 : ℕ) : ZMod (2 * N)) = a j := by
  have hj := ZMod.val_lt j
  have hlt : 2 * j.val + 1 < 2 * N := by omega
  rw [rightHalfVector, ZMod.val_natCast_of_lt hlt]
  have hmod : (2 * j.val + 1) % 2 = 1 := by omega
  have hdiv : (2 * j.val + 1) / 2 = j.val := by omega
  rw [hmod, ite_eq_left rfl, hdiv, ZMod.natCast_zmod_val]

theorem dyadicDetailVector_left (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (j : ZMod N) :
    dyadicDetailVector N a ((2 * j.val : ℕ) : ZMod (2 * N)) = a j := by
  unfold dyadicDetailVector cellDifference
  rw [rightHalfVector_even]
  have hcast : ((2 * j.val : ℕ) : ZMod (2 * N)) + 1 =
      ((2 * j.val + 1 : ℕ) : ZMod (2 * N)) := by push_cast; rfl
  rw [hcast, rightHalfVector_odd, sub_zero]

theorem dyadicDetailVector_right (N : ℕ) [NeZero N] (a : ZMod N → ℝ) (j : ZMod N) :
    dyadicDetailVector N a ((2 * j.val + 1 : ℕ) : ZMod (2 * N)) = -a j := by
  unfold dyadicDetailVector cellDifference
  rw [rightHalfVector_odd]
  have hp := successor_parity N (((2 * j.val + 1 : ℕ) : ZMod (2 * N)))
  have hj := ZMod.val_lt j
  have hlt : 2 * j.val + 1 < 2 * N := by omega
  rw [ZMod.val_natCast_of_lt hlt] at hp
  have hone : (2 * j.val + 1) % 2 = 1 := by omega
  rw [hone] at hp
  have hzero : rightHalfVector N a (((2 * j.val + 1 : ℕ) : ZMod (2 * N)) + 1) = 0 := by
    simp only [rightHalfVector, ite_eq_right hp]
  rw [hzero, zero_sub]

/-- The actual heat semigroup gains the full dyadic cancellation factor on
every finite linear combination of the Haar details at one generation. -/
theorem heat_dyadicDetail_sq {t : ℝ} (ht : 0 < t) (N : ℕ) [NeZero N] (a : ZMod N → ℝ) :
    ‖heat t (stepLp (2 * N) (dyadicDetailVector N a))‖ ^ 2 ≤
      min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) *
        ‖stepLp (2 * N) (dyadicDetailVector N a)‖ ^ 2 :=
  heat_cellDifference_sq ht (2 * N) (rightHalfVector N a) (rightHalfVector_disjoint N a)

theorem dyadicDetailVector_add (N : ℕ) (a b : ZMod N → ℝ) :
    dyadicDetailVector N (a + b) = dyadicDetailVector N a + dyadicDetailVector N b := by
  funext j
  dsimp [dyadicDetailVector, cellDifference, rightHalfVector]
  split_ifs <;> ring

theorem dyadicDetailVector_smul (N : ℕ) (c : ℝ) (a : ZMod N → ℝ) :
    dyadicDetailVector N (c • a) = c • dyadicDetailVector N a := by
  funext j
  dsimp [dyadicDetailVector, cellDifference, rightHalfVector]
  split_ifs <;> ring

theorem stepLp_add (N : ℕ) [NeZero N] (v w : ZMod N → ℝ) :
    stepLp N (v + w) = stepLp N v + stepLp N w := by
  apply Lp.ext
  filter_upwards [stepLp_ae N (v + w), stepLp_ae N v,
    stepLp_ae N w, Lp.coeFn_add (stepLp N v) (stepLp N w)] with x hd hv hw hs
  rw [hd, hs]
  simp only [Pi.add_apply, hv, hw]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ((v _ + w _ : ℝ) : ℂ) = (v _ : ℂ) + (w _ : ℂ)
  exact Complex.ofReal_add _ _

theorem stepLp_smul (N : ℕ) [NeZero N] (c : ℝ) (v : ZMod N → ℝ) :
    stepLp N (c • v) = c • stepLp N v := by
  apply Lp.ext
  filter_upwards [stepLp_ae N (c • v), stepLp_ae N v,
    Lp.coeFn_smul c (stepLp N v)] with x hd hv hs
  rw [hd, hs]
  simp only [Pi.smul_apply, hv]
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  change ((c * v _ : ℝ) : ℂ) = c • (v _ : ℂ)
  simp only [Complex.ofReal_mul, Complex.real_smul]

def detailLinear (N : ℕ) [NeZero N] : (ZMod N → ℝ) →ₗ[ℝ] CircleL2 where
  toFun a := stepLp (2 * N) (dyadicDetailVector N a)
  map_add' a b := by rw [dyadicDetailVector_add, stepLp_add]
  map_smul' c a := by rw [dyadicDetailVector_smul, stepLp_smul]; rfl

/-- The actual finite-dimensional Haar generation in circle `L²`. -/
def detailSpace (N : ℕ) [NeZero N] : Submodule ℝ CircleL2 := (detailLinear N).range

instance detailSpace_finiteDimensional (N : ℕ) [NeZero N] : FiniteDimensional ℝ (detailSpace N) :=
  LinearMap.finiteDimensional_range (detailLinear N)

/-- Orthogonal projection onto one genuine equal-cell Haar generation. -/
def detailProjection (N : ℕ) [NeZero N] : CircleL2 →L[ℝ] CircleL2 :=
  (detailSpace N).starProjection

theorem detailProjection_contraction (N : ℕ) [NeZero N] (f : CircleL2) :
    ‖detailProjection N f‖ ≤ ‖f‖ := (detailSpace N).norm_starProjection_apply_le f

theorem detailProjection_representation (N : ℕ) [NeZero N] (f : CircleL2) :
    ∃ a : ZMod N → ℝ, detailProjection N f = stepLp (2 * N) (dyadicDetailVector N a) := by
  have h := (detailSpace N).starProjection_apply_mem f
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha.symm⟩

/-- The actual dyadic heat projection bound, squared. Taking square roots
gives the standard `min(1, 2⁻ˡ t⁻¹/²)` cancellation estimate. -/
theorem heat_detailProjection_sq {t : ℝ} (ht : 0 < t) (N : ℕ) [NeZero N] (f : CircleL2) :
    ‖heat t (detailProjection N f)‖ ^ 2 ≤
      min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) * ‖f‖ ^ 2 := by
  obtain ⟨a, ha⟩ := detailProjection_representation N f
  have h := heat_dyadicDetail_sq ht N a
  rw [← ha] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (detailProjection_contraction N f) 2)
  apply le_min (by norm_num)
  positivity

def weightedFourierSq (w : ℤ → ℝ) (f : CircleL2) : ℝ :=
  ∑' n : ℤ, w n * ‖fourierCoeff f n‖ ^ 2

theorem weightedFourierSq_neg (w : ℤ → ℝ) (f : CircleL2) :
    weightedFourierSq w (-f) = weightedFourierSq w f := by
  unfold weightedFourierSq
  apply tsum_congr
  intro n
  rw [← fourierBasis_repr, map_neg]
  simp only [lp.coeFn_neg, Pi.neg_apply, norm_neg, fourierBasis_repr]

theorem weighted_heat_contraction (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (f : CircleL2) (hs : Summable (fun n : ℤ => w n * ‖fourierCoeff f n‖ ^ 2)) (t : ℝ) :
    Summable (fun n : ℤ => w n * ‖fourierCoeff (heat t f) n‖ ^ 2) ∧
      weightedFourierSq w (heat t f) ≤ weightedFourierSq w f := by
  have hterm (n : ℤ) : w n * ‖fourierCoeff (heat t f) n‖ ^ 2 ≤
      w n * ‖fourierCoeff f n‖ ^ 2 := by
    rw [heat_fourierCoeff, norm_mul, mul_pow]
    have hpow : ‖heatWeight t n‖ ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg _) (heatWeight_norm_le t n) 2
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (sq_nonneg _) hpow) (hw n)
  have hout := hs.of_nonneg_of_le (fun n => mul_nonneg (hw n) (sq_nonneg _)) hterm
  exact ⟨hout, hout.tsum_le_tsum hterm hs⟩

theorem weighted_heat_translation_difference {t : ℝ} (ht : 0 < t)
    (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) (h : ℝ) (f : CircleL2)
    (hs : Summable (fun n : ℤ => w n * ‖fourierCoeff f n‖ ^ 2)) :
    Summable (fun n : ℤ => w n * ‖fourierCoeff (heat t (f - translate h f)) n‖ ^ 2) ∧
      weightedFourierSq w (heat t (f - translate h f)) ≤
        h ^ 2 / (2 * t) * weightedFourierSq w f := by
  have hterm (n : ℤ) : w n * ‖fourierCoeff (heat t (f - translate h f)) n‖ ^ 2 ≤
      h ^ 2 / (2 * t) * (w n * ‖fourierCoeff f n‖ ^ 2) := by
    rw [heat_fourierCoeff, difference_fourierCoeff, ← mul_assoc, norm_mul, mul_pow]
    have hb := mul_le_mul_of_nonneg_right (heat_translation_multiplier ht h n)
      (sq_nonneg ‖fourierCoeff f n‖)
    have hm := mul_le_mul_of_nonneg_left hb (hw n)
    simpa only [mul_assoc, mul_left_comm (w n)] using hm
  have hout := (hs.mul_left (h ^ 2 / (2 * t))).of_nonneg_of_le
    (fun n => mul_nonneg (hw n) (sq_nonneg _)) hterm
  refine ⟨hout, ?_⟩
  unfold weightedFourierSq
  rw [← tsum_mul_left]
  exact hout.tsum_le_tsum hterm (hs.mul_left _)

theorem stepLp_fourierCoeff (N : ℕ) [NeZero N] (v : ZMod N → ℝ) (n : ℤ) :
    fourierCoeff (stepLp N v) n = fourierCoeff (CircleStep.circleStep N v) n :=
  congrFun (fourierCoeff_congr_ae (stepLp_ae N v)) n

def massiveWeight (κ Λ ρ : ℝ) (n : ℤ) : ℝ := (Λ + (κ * (n : ℝ)) ^ 2) ^ ρ

theorem massiveWeight_nonneg {Λ : ℝ} (hΛ : 0 ≤ Λ) (κ ρ : ℝ) (n : ℤ) :
    0 ≤ massiveWeight κ Λ ρ n := Real.rpow_nonneg (add_nonneg hΛ (sq_nonneg _)) _

def inverseConstant (κ ρ : ℝ) : ℝ := 1 + κ ^ (2 * ρ) * CircleStep.fractionalInverseConstant ρ

theorem inverseConstant_nonneg {κ ρ : ℝ} (hκ : 0 ≤ κ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    0 ≤ inverseConstant κ ρ :=
  add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg hκ _)
    (CircleStep.fractionalInverseConstant_nonneg hρ hρhalf))

theorem summable_stepLp_massive (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    Summable (fun n : ℤ => massiveWeight κ Λ ρ n * ‖fourierCoeff (stepLp N v) n‖ ^ 2) := by
  simpa only [massiveWeight, stepLp_fourierCoeff] using
    CircleStep.summable_circleStep_massive N v hκ hΛ hρ hρhalf

theorem stepLp_massive_inverse (N : ℕ) [NeZero N] (v : ZMod N → ℝ)
    {κ Λ ρ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2) :
    weightedFourierSq (massiveWeight κ Λ ρ) (stepLp N v) ≤
      inverseConstant κ ρ * (Λ + (N : ℝ) ^ 2) ^ ρ * ‖stepLp N v‖ ^ 2 := by
  have h := CircleStep.circleStep_massive_spectral_inverse N v hκ hΛ hρ hρhalf
  rw [CircleStep.circleStep_L2] at h
  rw [stepLp_norm_sq]
  simpa only [weightedFourierSq, massiveWeight, stepLp_fourierCoeff, inverseConstant,
    CircleStep.massiveFourierSq, CyclicStep.stepL2Sq, FiniteTransport.vectorSq] using h

/-- Full massive Sobolev heat cancellation on the literal dyadic detail
space. The Fourier weight may use either physical or normalized frequencies. -/
theorem massive_heat_dyadicDetail {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (N : ℕ) [NeZero N] (a : ZMod N → ℝ) :
    weightedFourierSq (massiveWeight κ Λ ρ)
      (heat t (stepLp (2 * N) (dyadicDetailVector N a))) ≤
      inverseConstant κ ρ * (Λ + ((2 * N : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) *
          ‖stepLp (2 * N) (dyadicDetailVector N a)‖ ^ 2 := by
  let w := massiveWeight κ Λ ρ
  let g := stepLp (2 * N) (rightHalfVector N a)
  let d := stepLp (2 * N) (dyadicDetailVector N a)
  let A := inverseConstant κ ρ * (Λ + ((2 * N : ℕ) : ℝ) ^ 2) ^ ρ
  have hA : 0 ≤ A := mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (by positivity)
  have hw : ∀ n, 0 ≤ w n := massiveWeight_nonneg hΛ κ ρ
  have hnorm : ‖d‖ ^ 2 = 2 * ‖g‖ ^ 2 :=
    cellDifference_norm_sq (2 * N) _ (rightHalfVector_disjoint N a)
  have hd : d = -(g - translate (((2 * N : ℕ) : ℝ)⁻¹) g) := by
    dsimp only [d, g, dyadicDetailVector]
    rw [stepLp_cellDifference]
    abel
  have hcoarse : weightedFourierSq w (heat t d) ≤ A * ‖d‖ ^ 2 :=
    (weighted_heat_contraction w hw d
      (summable_stepLp_massive _ _ hκ hΛ hρ hρhalf) t).2.trans
      (stepLp_massive_inverse _ _ hκ hΛ hρ hρhalf)
  have hfine := (weighted_heat_translation_difference ht w hw
    (((2 * N : ℕ) : ℝ)⁻¹) g (summable_stepLp_massive _ _ hκ hΛ hρ hρhalf)).2
  have hg := stepLp_massive_inverse (2 * N) (rightHalfVector N a) hκ hΛ hρ hρhalf
  change weightedFourierSq w g ≤ A * ‖g‖ ^ 2 at hg
  have hheat : weightedFourierSq w (heat t d) =
      weightedFourierSq w (heat t (g - translate (((2 * N : ℕ) : ℝ)⁻¹) g)) := by
    rw [hd, map_neg, weightedFourierSq_neg]
  have hfine' : weightedFourierSq w (heat t d) ≤
      A * ((((2 * N : ℕ) : ℝ)⁻¹) ^ 2 / (4 * t)) * ‖d‖ ^ 2 := by
    rw [hheat]
    apply hfine.trans
    calc
      _ ≤ (((2 * N : ℕ) : ℝ)⁻¹) ^ 2 / (2 * t) * (A * ‖g‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by rw [hnorm]; field_simp; ring
  change weightedFourierSq w (heat t d) ≤ A * min 1 _ * ‖d‖ ^ 2
  rw [mul_min_of_nonneg _ _ hA, min_mul_of_nonneg _ _ (sq_nonneg _), mul_one]
  exact le_min hcoarse hfine'

theorem summable_massive_heat_detailProjection {t κ Λ ρ : ℝ}
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (N : ℕ) [NeZero N] (f : CircleL2) :
    Summable (fun n : ℤ => massiveWeight κ Λ ρ n *
      ‖fourierCoeff (heat t (detailProjection N f)) n‖ ^ 2) := by
  obtain ⟨a, ha⟩ := detailProjection_representation N f
  rw [ha]
  exact (weighted_heat_contraction _ (massiveWeight_nonneg hΛ κ ρ) _
    (summable_stepLp_massive _ _ hκ hΛ hρ hρhalf) t).1

theorem massive_heat_detailProjection {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (N : ℕ) [NeZero N] (f : CircleL2) :
    weightedFourierSq (massiveWeight κ Λ ρ) (heat t (detailProjection N f)) ≤
      inverseConstant κ ρ * (Λ + ((2 * N : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) * ‖f‖ ^ 2 := by
  obtain ⟨a, ha⟩ := detailProjection_representation N f
  have h := massive_heat_dyadicDetail ht hκ hΛ hρ hρhalf N a
  rw [← ha] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (detailProjection_contraction N f) 2)
  exact mul_nonneg (mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (by positivity))
    (le_min (by norm_num) (by positivity))

/-- Finite Hilbert--Schmidt column estimate for the actual heat projection
into the massive Sobolev Fourier space. -/
theorem massive_heat_detailProjection_sum {ι : Type*} (I : Finset ι)
    {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (N : ℕ) [NeZero N] (f : ι → CircleL2) :
    (∑ j ∈ I, weightedFourierSq (massiveWeight κ Λ ρ) (heat t (detailProjection N (f j)))) ≤
      inverseConstant κ ρ * (Λ + ((2 * N : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) * (∑ j ∈ I, ‖f j‖ ^ 2) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => massive_heat_detailProjection ht hκ hΛ hρ hρhalf N (f j))

end CircleHeat

namespace FiniteHaar

open MeasureTheory AddCircle Finset FiniteTransport CircleHeat Matrix
open scoped ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Canonical left-to-right spatial order on the recursive binary leaves. -/
def gridFinEquiv : (n : ℕ) → Grid n ≃ Fin (2 ^ n)
  | 0 => by change Unit ≃ Fin 1; exact Equiv.ofUnique _ _
  | n + 1 => (Equiv.sumCongr (gridFinEquiv n) (gridFinEquiv n)).trans
      (finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega)))

def gridCellEquiv (n : ℕ) : Grid n ≃ ZMod (2 ^ n) :=
  (gridFinEquiv n).trans (ZMod.finEquiv (2 ^ n)).toEquiv

/-- The fixed ordinary Haar synthesis, as literal periodic step functions.
The normalization accounts for the cell measure `2⁻ⁿ`. -/
def referenceSynthesis (n : ℕ) (x : Option (DetailIndex n) → ℝ) : CircleL2 :=
  stepLp (2 ^ n) (fun j => Real.sqrt ((2 ^ n : ℕ) : ℝ) *
    (haarMatrix n (fun _ => 1) *ᵥ x) ((gridCellEquiv n).symm j))

theorem referenceSynthesis_norm_sq (n : ℕ) (x : Option (DetailIndex n) → ℝ) :
    ‖referenceSynthesis n x‖ ^ 2 = vectorSq x := by
  have hN : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
  rw [referenceSynthesis, stepLp_norm_sq]
  simp_rw [mul_pow, Real.sq_sqrt hN.le]
  rw [← mul_sum]
  have hsum : (∑ j : ZMod (2 ^ n), ((haarMatrix n (fun _ => 1) *ᵥ x)
      ((gridCellEquiv n).symm j)) ^ 2) = vectorSq (haarMatrix n (fun _ => 1) *ᵥ x) :=
    Equiv.sum_comp (gridCellEquiv n).symm (fun y => ((haarMatrix n (fun _ => 1) *ᵥ x) y) ^ 2)
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul, referenceHaar_vectorSq]

theorem referenceHaar_mul_referenceFactor (n : ℕ) (c : Grid n → ℝ) :
    haarMatrix n (fun _ => 1) * referenceFactor n c = localFactor n c := by
  rw [referenceFactor, ← Matrix.mul_assoc, referenceHaar_coorthogonal, Matrix.one_mul]

/-- The signed columns are actual physical weighted-Haar factor differences,
written through the fixed isometric reference synthesis. -/
def signedColumn (n : ℕ) (c d : Grid n → ℝ) (j : Option (DetailIndex n)) : CircleL2 :=
  referenceSynthesis n (fun i => referenceFactor n c i j - referenceFactor n d i j)

theorem signedColumn_ae (n : ℕ) (c d : Grid n → ℝ) (j : Option (DetailIndex n)) :
    signedColumn n c d j =ᵐ[haarAddCircle]
      CircleStep.circleStep (2 ^ n) (fun k => Real.sqrt ((2 ^ n : ℕ) : ℝ) *
        (localFactor n c ((gridCellEquiv n).symm k) j -
          localFactor n d ((gridCellEquiv n).symm k) j)) := by
  have heq (y : Grid n) : (haarMatrix n (fun _ => 1) *ᵥ
      (fun i => referenceFactor n c i j - referenceFactor n d i j)) y =
      localFactor n c y j - localFactor n d y j := by
    change (∑ i, haarMatrix n (fun _ => 1) y i *
      (referenceFactor n c i j - referenceFactor n d i j)) = _
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    change (haarMatrix n (fun _ => 1) * referenceFactor n c) y j -
      (haarMatrix n (fun _ => 1) * referenceFactor n d) y j = _
    rw [referenceHaar_mul_referenceFactor, referenceHaar_mul_referenceFactor]
  change stepLp _ _ =ᵐ[haarAddCircle] _
  have h := stepLp_ae (2 ^ n) (fun k => Real.sqrt ((2 ^ n : ℕ) : ℝ) *
    (haarMatrix n (fun _ => 1) *ᵥ
      (fun i => referenceFactor n c i j - referenceFactor n d i j)) ((gridCellEquiv n).symm k))
  simpa only [heq] using h

theorem signedColumn_sum_norm_sq (n : ℕ) (c d : Grid n → ℝ) :
    (∑ j : Option (DetailIndex n), ‖signedColumn n c d j‖ ^ 2) =
      frobeniusSq (referenceFactor n c - referenceFactor n d) := by
  simp only [signedColumn, referenceSynthesis_norm_sq, vectorSq, frobeniusSq, Matrix.sub_apply]
  exact sum_comm

theorem signedColumn_sum_norm_sq_le (n : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), ‖signedColumn n c d j‖ ^ 2) ≤
      U / m ^ 2 * ∑ x, (c x - d x) ^ 2 := by
  rw [signedColumn_sum_norm_sq]
  exact referenceFactor_signed_frobeniusSq n c d m U hm hc hd

/-- A concrete signed finite-prefix heat Hilbert--Schmidt bound. Every
column is the explicitly constructed weighted Haar difference on the
physical periodic grid; every output is the actual heat/detail projection
in the full massive Fourier norm. -/
theorem signed_massive_heat_detail_HS {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (N : ℕ) [NeZero N] (n : ℕ) (c d : Grid n → ℝ)
    (m U : ℝ) (hm : 0 < m)
    (hc : ∀ x, m ≤ c x ∧ c x ≤ U) (hd : ∀ x, m ≤ d x ∧ d x ≤ U) :
    (∑ j : Option (DetailIndex n), weightedFourierSq (massiveWeight κ Λ ρ)
      (heat t (detailProjection N (signedColumn n c d j)))) ≤
      inverseConstant κ ρ * (Λ + ((2 * N : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * N : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) *
          (U / m ^ 2 * ∑ x, (c x - d x) ^ 2) := by
  have h := massive_heat_detailProjection_sum Finset.univ ht hκ hΛ hρ hρhalf N (signedColumn n c d)
  apply h.trans
  apply mul_le_mul_of_nonneg_left (signedColumn_sum_norm_sq_le n c d m U hm hc hd)
  exact mul_nonneg (mul_nonneg (inverseConstant_nonneg hκ hρ hρhalf) (by positivity))
    (le_min (by norm_num) (by positivity))

/-- Generation, with the constant mode at zero and the root detail at one. -/
def detailLevel : (n : ℕ) → DetailIndex n → ℕ
  | 0, j => nomatch j
  | _ + 1, Sum.inl _ => 1
  | n + 1, Sum.inr (Sum.inl j) => detailLevel n j + 1
  | n + 1, Sum.inr (Sum.inr j) => detailLevel n j + 1

def modeLevel (n : ℕ) : Option (DetailIndex n) → ℕ
  | none => 0
  | some j => detailLevel n j

theorem detailLevel_pos (n : ℕ) (j : DetailIndex n) : 0 < detailLevel n j := by
  induction n with
  | zero => exact Empty.elim j
  | succ n ih => rcases j with _ | (_ | _) <;> simp only [detailLevel] <;> omega

/-- The stronger block triangularity by generation, including branches in
either spatial order. This is what permits actual coarse-output prefixes. -/
theorem mixed_detail_finer_zero (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i j : DetailIndex n) (hij : detailLevel n i < detailLevel n j) :
    weightedInner c (detailColumn n (fun _ => 1) i) (detailColumn n c j) = 0 := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    dsimp only [Grid, DetailIndex, gridFintype, detailFintype] at c hc i j ⊢
    have hcl : ∀ x, 0 < c (Sum.inl x) := fun x => hc (Sum.inl x)
    have hcr : ∀ x, 0 < c (Sum.inr x) := fun x => hc (Sum.inr x)
    rcases i with ⟨⟩ | (i | i) <;> rcases j with ⟨⟩ | (j | j)
    · simp only [detailLevel] at hij; omega
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_const_left, detailColumn_cancellation n _ hcl,
        weightedInner_zero_right, mul_zero, add_zero]
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_right, weightedInner_const_left,
        detailColumn_cancellation n _ hcr, mul_zero, zero_add]
    · simp only [detailLevel] at hij; omega
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, add_zero]
      exact ih _ hcl i j (by simpa only [detailLevel, Nat.add_lt_add_iff_right] using hij)
    · simp only [detailColumn]
      erw [weightedInner_sum]
      simp only [weightedInner_zero_left, weightedInner_zero_right, add_zero]
    · simp only [detailLevel] at hij; omega
    · simp only [detailColumn]
      erw [weightedInner_sum]
      simp only [weightedInner_zero_left, weightedInner_zero_right, add_zero]
    · simp only [detailColumn]
      erw [weightedInner_sum]
      rw [weightedInner_zero_left, zero_add]
      exact ih _ hcr i j (by simpa only [detailLevel, Nat.add_lt_add_iff_right] using hij)

theorem referenceFactor_finer_zero (n : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i j : Option (DetailIndex n)) (hij : modeLevel n i < modeLevel n j) :
    referenceFactor n c i j = 0 := by
  rw [referenceFactor_apply]
  cases i with
  | none =>
    cases j with
    | none => simp only [modeLevel] at hij; omega
    | some j =>
      simp only [haarColumn]
      rw [weightedInner_const_left, detailColumn_cancellation n c hc j, mul_zero]
  | some i =>
    cases j with
    | none => simp only [modeLevel] at hij; omega
    | some j => exact mixed_detail_finer_zero n c hc i j hij

theorem referenceFactor_prefix_zero (n k : ℕ) (c : Grid n → ℝ) (hc : ∀ x, 0 < c x)
    (i : {i : Option (DetailIndex n) // modeLevel n i ≤ k})
    (j : Option (DetailIndex n)) (hj : ¬modeLevel n j ≤ k) :
    referenceFactor n c i.val j = 0 :=
  referenceFactor_finer_zero n c hc i.val j (lt_of_le_of_lt i.property (lt_of_not_ge hj))

theorem totalMass_one (n : ℕ) : totalMass n (fun _ => (1 : ℝ)) = ((2 ^ n : ℕ) : ℝ) := by
  simp only [totalMass, sum_const, card_univ, nsmul_eq_mul, mul_one, card_grid]

theorem constantColumn_sq (n : ℕ) (x : Grid n) :
    (haarColumn n (fun _ => 1) none x) ^ 2 = (((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [haarColumn, totalMass_one, inv_pow, Real.sq_sqrt (by positivity)]

theorem rootLeft_sq (n : ℕ) :
    (haarLeft (totalMass n (fun _ => 1)) (totalMass n (fun _ => 1))) ^ 2 =
      (((2 ^ (n + 1) : ℕ) : ℝ))⁻¹ := by
  have hM : 0 < totalMass n (fun _ => (1 : ℝ)) := totalMass_pos n _ (fun _ => zero_lt_one)
  rw [haarLeft_formula hM hM, Real.sq_sqrt (by positivity), totalMass_one]
  push_cast
  rw [pow_succ]
  field_simp
  ring

theorem rootRight_sq (n : ℕ) :
    (haarRight (totalMass n (fun _ => 1)) (totalMass n (fun _ => 1))) ^ 2 =
      (((2 ^ (n + 1) : ℕ) : ℝ))⁻¹ := by
  have hr : haarRight (totalMass n (fun _ => (1 : ℝ))) (totalMass n (fun _ => 1)) =
      -haarLeft (totalMass n (fun _ => 1)) (totalMass n (fun _ => 1)) := by
    unfold haarRight haarLeft
    ring
  rw [hr, neg_sq, rootLeft_sq]

def detailPrefixSq (n k : ℕ) (x : Grid n) : ℝ :=
  ∑ i : DetailIndex n, if detailLevel n i ≤ k then (detailColumn n (fun _ => 1) i x) ^ 2 else 0

theorem detailPrefixSq_zero (n : ℕ) (x : Grid n) : detailPrefixSq n 0 x = 0 := by
  apply sum_eq_zero
  intro i hi
  exact ite_eq_right (not_le.mpr (detailLevel_pos n i))

def prefixSq (n k : ℕ) (x : Grid n) : ℝ :=
  ∑ i : Option (DetailIndex n), if modeLevel n i ≤ k then (haarMatrix n (fun _ => 1) x i) ^ 2 else 0

theorem prefixSq_eq (n k : ℕ) (x : Grid n) :
    prefixSq n k x = (((2 ^ n : ℕ) : ℝ))⁻¹ + detailPrefixSq n k x := by
  rw [prefixSq, Fintype.sum_option]
  simp only [modeLevel, zero_le, ite_true, haarMatrix]
  rw [constantColumn_sq]
  rfl

theorem detailPrefixSq_succ_left (n k : ℕ) (x : Grid n) :
    detailPrefixSq (n + 1) (k + 1) (Sum.inl x) =
      (((2 ^ (n + 1) : ℕ) : ℝ))⁻¹ + detailPrefixSq n k x := by
  unfold detailPrefixSq
  dsimp only [DetailIndex, detailFintype]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [detailLevel, detailColumn, Sum.elim_inl,
    Nat.succ_le_succ_iff, Nat.zero_le, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    ite_true, ite_self, sum_const_zero, add_zero, Fintype.sum_unique]
  rw [rootLeft_sq]

theorem detailPrefixSq_succ_right (n k : ℕ) (x : Grid n) :
    detailPrefixSq (n + 1) (k + 1) (Sum.inr x) =
      (((2 ^ (n + 1) : ℕ) : ℝ))⁻¹ + detailPrefixSq n k x := by
  unfold detailPrefixSq
  dsimp only [DetailIndex, detailFintype]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [detailLevel, detailColumn, Sum.elim_inr,
    Nat.succ_le_succ_iff, Nat.zero_le, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    ite_true, ite_self, sum_const_zero, zero_add, Fintype.sum_unique]
  rw [rootRight_sq]

theorem prefixSq_zero (n : ℕ) (x : Grid n) :
    prefixSq n 0 x = (((2 ^ n : ℕ) : ℝ))⁻¹ := by
  rw [prefixSq_eq, detailPrefixSq_zero, add_zero]

theorem prefixSq_succ_left (n k : ℕ) (x : Grid n) :
    prefixSq (n + 1) (k + 1) (Sum.inl x) = prefixSq n k x := by
  rw [prefixSq_eq, detailPrefixSq_succ_left, prefixSq_eq]
  have hp : (((2 ^ (n + 1) : ℕ) : ℝ)) = 2 * (((2 ^ n : ℕ) : ℝ)) := by
    simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hp]
  field_simp
  ring

theorem prefixSq_succ_right (n k : ℕ) (x : Grid n) :
    prefixSq (n + 1) (k + 1) (Sum.inr x) = prefixSq n k x := by
  rw [prefixSq_eq, detailPrefixSq_succ_right, prefixSq_eq]
  have hp : (((2 ^ (n + 1) : ℕ) : ℝ)) = 2 * (((2 ^ n : ℕ) : ℝ)) := by
    simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hp]
  field_simp
  ring

/-- Exact generation-prefix Christoffel bound. It is independent of the
fine resolution `n`; after the physical normalization it is simply `2^k`. -/
theorem prefixSq_le (n k : ℕ) (x : Grid n) :
    prefixSq n k x ≤ (((2 ^ k : ℕ) : ℝ)) / (((2 ^ n : ℕ) : ℝ)) := by
  induction n generalizing k with
  | zero =>
    have hzero : detailPrefixSq 0 k x = 0 := by
      apply sum_eq_zero
      intro i hi
      exact Empty.elim i
    rw [prefixSq_eq, hzero]
    simp only [pow_zero, Nat.cast_one, inv_one, add_zero, div_one]
    have hp : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hp
  | succ n ih =>
    cases k with
    | zero => rw [prefixSq_zero]; simp only [pow_zero, Nat.cast_one, one_div, le_refl]
    | succ k =>
      have hp : (((2 ^ (k + 1) : ℕ) : ℝ)) / (((2 ^ (n + 1) : ℕ) : ℝ)) =
          (((2 ^ k : ℕ) : ℝ)) / (((2 ^ n : ℕ) : ℝ)) := by
        simp only [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        field_simp
      rcases x with x | x
      · rw [prefixSq_succ_left, hp]
        exact ih k x
      · rw [prefixSq_succ_right, hp]
        exact ih k x

theorem referenceHaar_prefix_row_bound (n k : ℕ) (x : Grid n) :
    (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      (haarMatrix n (fun _ => 1) x i.val) ^ 2) ≤
        (((2 ^ k : ℕ) : ℝ)) / (((2 ^ n : ℕ) : ℝ)) := by
  classical
  have heq : (∑ i : {i : Option (DetailIndex n) // modeLevel n i ≤ k},
      (haarMatrix n (fun _ => 1) x i.val) ^ 2) = prefixSq n k x := by
    rw [prefixSq, ← Finset.sum_subtype (univ.filter (fun i => modeLevel n i ≤ k))
      (by simp) (fun i => (haarMatrix n (fun _ => 1) x i) ^ 2)]
    rw [Finset.sum_filter]
  rw [heq]
  exact prefixSq_le n k x

end FiniteHaar

namespace CircleStep
open MeasureTheory AddCircle Set
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem circle_cell_representation (N : ℕ) [NeZero N] (x : AddCircle (1 : ℝ)) :
    ∃ j : ZMod N, ∃ u : ℝ, u ∈ Ioc (0 : ℝ) 1 ∧
      x = ((((j.val : ℝ) + u) / N : ℝ) : AddCircle (1 : ℝ)) := by
  let y := AddCircle.equivIoc (1 : ℝ) 0 x
  have hy : (y : ℝ) ∈ Ioc (0 : ℝ) 1 := by simpa only [zero_add] using y.property
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  let b : ℤ := ⌈(N : ℝ) * (y : ℝ)⌉ - 1
  have hb0 : 0 ≤ b := by
    have hp := Int.ceil_pos.mpr (mul_pos hN hy.1)
    dsimp only [b]
    omega
  have hbN : b < N := by
    have hp : ⌈(N : ℝ) * (y : ℝ)⌉ ≤ (N : ℤ) :=
      Int.ceil_le.mpr (by exact mul_le_of_le_one_right hN.le hy.2)
    dsimp only [b]
    omega
  let j : ZMod N := (b.toNat : ℕ)
  have hj : j.val = b.toNat := ZMod.val_natCast_of_lt (by omega)
  have hbcast : (b.toNat : ℝ) = (b : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hb0
  have hc := Int.ceil_eq_iff.mp (rfl : ⌈(N : ℝ) * (y : ℝ)⌉ = ⌈(N : ℝ) * (y : ℝ)⌉)
  have hbr : (b : ℝ) = (⌈(N : ℝ) * (y : ℝ)⌉ : ℝ) - 1 := by dsimp only [b]; push_cast; rfl
  refine ⟨j, (N : ℝ) * (y : ℝ) - j.val, ?_, ?_⟩
  · rw [hj, hbcast, hbr]
    constructor <;> linarith [hc.1, hc.2]
  · have heq : ((j.val : ℝ) + ((N : ℝ) * (y : ℝ) - j.val)) / N = (y : ℝ) := by
      field_simp
      ring
    rw [heq]
    exact AddCircle.coe_equivIoc.symm

theorem realStep_refine_cell (N M : ℕ) [NeZero N] [NeZero M]
    (v : ZMod N → ℝ) (j : ZMod N) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    realStep (N * M) (fun i => v (((i.val / M : ℕ) : ZMod N)))
      (((j.val : ℝ) + u) / N) = v j := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  let b : ℤ := ⌈(M : ℝ) * u⌉ - 1
  have hb0 : 0 ≤ b := by
    have hp := Int.ceil_pos.mpr (mul_pos hM hu.1)
    dsimp only [b]
    omega
  have hbM : b < M := by
    have hp : ⌈(M : ℝ) * u⌉ ≤ (M : ℤ) :=
      Int.ceil_le.mpr (mul_le_of_le_one_right hM.le hu.2)
    dsimp only [b]
    omega
  have hbcast : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
  have hscale : ((N * M : ℕ) : ℝ) * (((j.val : ℝ) + u) / N) =
      (M : ℝ) * u + ((M * j.val : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  unfold realStep
  rw [hscale, Int.ceil_add_natCast]
  have hidx : ⌈(M : ℝ) * u⌉ + ((M * j.val : ℕ) : ℤ) - 1 =
      ((M * j.val + b.toNat : ℕ) : ℤ) := by
    push_cast
    rw [hbcast]
    dsimp only [b]
    ring
  rw [hidx, Int.cast_natCast]
  have hj := ZMod.val_lt j
  have hlt : M * j.val + b.toNat < N * M := by
    have hbM' : b.toNat < M := by omega
    nlinarith
  dsimp only
  rw [ZMod.val_natCast_of_lt hlt]
  have hdiv : (M * j.val + b.toNat) / M = j.val := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · have hbM' : b.toNat < M := by omega
      nlinarith
  rw [hdiv, ZMod.natCast_zmod_val]

/-- A periodic step function is literally unchanged when each cell is
subdivided into any positive number of equal cells. -/
theorem circleStep_refine (N M : ℕ) [NeZero N] [NeZero M] (v : ZMod N → ℝ) :
    circleStep (N * M) (fun i => v (((i.val / M : ℕ) : ZMod N))) = circleStep N v := by
  funext x
  obtain ⟨j, u, hu, rfl⟩ := circle_cell_representation N x
  rw [circleStep_coe, circleStep_coe, realStep_refine_cell N M v j hu, realStep_cell N v j hu]

theorem circleStep_refine_of_eq (N M K : ℕ) [NeZero N] [NeZero M]
    (hK : K = N * M) (v : ZMod N → ℝ) :
    circleStep K (fun i => v (((i.val / M : ℕ) : ZMod N))) = circleStep N v := by
  subst K
  exact circleStep_refine N M v

end CircleStep

namespace FiniteHaar
open Finset Matrix MeasureTheory AddCircle CircleHeat
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Remove the last binary digit, preserving the spatial order. -/
def leafParent : (n : ℕ) → Grid (n + 1) → Grid n
  | 0, _ => ()
  | n + 1, Sum.inl x => Sum.inl (leafParent n x)
  | n + 1, Sum.inr x => Sum.inr (leafParent n x)

def detailEmbed : (n : ℕ) → DetailIndex n → DetailIndex (n + 1)
  | 0, i => nomatch i
  | _ + 1, Sum.inl _ => Sum.inl ()
  | n + 1, Sum.inr (Sum.inl i) => Sum.inr (Sum.inl (detailEmbed n i))
  | n + 1, Sum.inr (Sum.inr i) => Sum.inr (Sum.inr (detailEmbed n i))

def modeEmbed (n : ℕ) : Option (DetailIndex n) → Option (DetailIndex (n + 1))
  | none => none
  | some i => some (detailEmbed n i)

def gridOrdinal (n : ℕ) (x : Grid n) : ℕ := (gridFinEquiv n x).val

theorem gridOrdinal_left (n : ℕ) (x : Grid n) :
    gridOrdinal (n + 1) (Sum.inl x) = gridOrdinal n x := by
  rfl

theorem gridOrdinal_right (n : ℕ) (x : Grid n) :
    gridOrdinal (n + 1) (Sum.inr x) = 2 ^ n + gridOrdinal n x := by
  rfl

theorem gridCellEquiv_val (n : ℕ) (x : Grid n) : (gridCellEquiv n x).val = gridOrdinal n x := by
  have hfin (N : ℕ) [NeZero N] (j : Fin N) : (ZMod.finEquiv N j).val = j.val := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ N => rfl
  exact hfin (2 ^ n) (gridFinEquiv n x)

theorem leafParent_ordinal (n : ℕ) (x : Grid (n + 1)) :
    gridOrdinal n (leafParent n x) = gridOrdinal (n + 1) x / 2 := by
  induction n with
  | zero =>
    rcases x with x | x <;> cases x <;> rfl
  | succ n ih =>
    rcases x with x | x
    · rw [leafParent, gridOrdinal_left, gridOrdinal_left]
      exact ih x
    · rw [leafParent, gridOrdinal_right, gridOrdinal_right, ih]
      rw [pow_succ, Nat.mul_comm (2 ^ n) 2, Nat.mul_add_div (by norm_num : 0 < 2)]

theorem uniformRoot_left (n : ℕ) :
    haarLeft (totalMass n (fun _ => 1)) (totalMass n (fun _ => 1)) =
      (Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)))⁻¹ := by
  have hL := haarLeft_pos
    (totalMass_pos n (fun _ => (1 : ℝ)) (fun _ => zero_lt_one))
    (totalMass_pos n (fun _ => (1 : ℝ)) (fun _ => zero_lt_one))
  have hs : 0 < (Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)))⁻¹ := by positivity
  have hsq := rootLeft_sq n
  have hi : ((Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)))⁻¹) ^ 2 =
      (((2 ^ (n + 1) : ℕ) : ℝ))⁻¹ := by rw [inv_pow, Real.sq_sqrt (by positivity)]
  nlinarith

theorem uniformRoot_right (n : ℕ) :
    haarRight (totalMass n (fun _ => 1)) (totalMass n (fun _ => 1)) =
      -(Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)))⁻¹ := by
  rw [← uniformRoot_left]
  unfold haarRight haarLeft
  ring

theorem sqrt_grid_succ (n : ℕ) :
    Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)) = Real.sqrt 2 * Real.sqrt (((2 ^ n : ℕ) : ℝ)) := by
  rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm, Real.sqrt_mul (by positivity)]

theorem inv_sqrt_grid_succ (n : ℕ) :
    (Real.sqrt (((2 ^ (n + 1) : ℕ) : ℝ)))⁻¹ =
      (Real.sqrt 2)⁻¹ * (Real.sqrt (((2 ^ n : ℕ) : ℝ)))⁻¹ := by
  rw [sqrt_grid_succ, _root_.mul_inv_rev, mul_comm]

theorem detailColumn_refine (n : ℕ) (i : DetailIndex n) (x : Grid (n + 1)) :
    detailColumn (n + 1) (fun _ => 1) (detailEmbed n i) x =
      (Real.sqrt 2)⁻¹ * detailColumn n (fun _ => 1) i (leafParent n x) := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i) <;> rcases x with x | x
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent]
      rw [uniformRoot_left, uniformRoot_left, inv_sqrt_grid_succ]
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent]
      rw [uniformRoot_right, uniformRoot_right, inv_sqrt_grid_succ]
      ring
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent]
      exact ih i x
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent, mul_zero]
    · simp only [detailEmbed, detailColumn, Sum.elim_inl, leafParent, mul_zero]
    · simp only [detailEmbed, detailColumn, Sum.elim_inr, leafParent]
      exact ih i x

theorem haarColumn_refine (n : ℕ) (i : Option (DetailIndex n)) (x : Grid (n + 1)) :
    haarColumn (n + 1) (fun _ => 1) (modeEmbed n i) x =
      (Real.sqrt 2)⁻¹ * haarColumn n (fun _ => 1) i (leafParent n x) := by
  cases i with
  | none => simp only [modeEmbed, haarColumn, totalMass_one, inv_sqrt_grid_succ]
  | some i => exact detailColumn_refine n i x

def normalizedColumn (n : ℕ) (i : Option (DetailIndex n)) (x : Grid n) : ℝ :=
  Real.sqrt (((2 ^ n : ℕ) : ℝ)) * haarColumn n (fun _ => 1) i x

theorem normalizedColumn_refine (n : ℕ) (i : Option (DetailIndex n)) (x : Grid (n + 1)) :
    normalizedColumn (n + 1) (modeEmbed n i) x = normalizedColumn n i (leafParent n x) := by
  rw [normalizedColumn, haarColumn_refine, sqrt_grid_succ, normalizedColumn]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

def ordinaryColumn (n : ℕ) (i : Option (DetailIndex n)) : CircleL2 :=
  stepLp (2 ^ n) (fun j => normalizedColumn n i ((gridCellEquiv n).symm j))

theorem ordinaryColumn_refine (n : ℕ) (i : Option (DetailIndex n)) :
    ordinaryColumn (n + 1) (modeEmbed n i) = ordinaryColumn n i := by
  apply Lp.ext
  have hleft := stepLp_ae (2 ^ (n + 1))
    (fun j => normalizedColumn (n + 1) (modeEmbed n i) ((gridCellEquiv (n + 1)).symm j))
  have hright := stepLp_ae (2 ^ n) (fun j => normalizedColumn n i ((gridCellEquiv n).symm j))
  apply hleft.trans
  apply Filter.EventuallyEq.trans _ hright.symm
  apply ae_of_all
  intro x
  have harray : (fun j : ZMod (2 ^ (n + 1)) =>
      normalizedColumn (n + 1) (modeEmbed n i) ((gridCellEquiv (n + 1)).symm j)) =
      (fun j => normalizedColumn n i ((gridCellEquiv n).symm
        (((j.val / 2 : ℕ) : ZMod (2 ^ n))))) := by
    funext j
    rw [normalizedColumn_refine]
    congr 1
    apply (gridCellEquiv n).injective
    apply ZMod.val_injective
    rw [gridCellEquiv_val, leafParent_ordinal]
    have hj : gridOrdinal (n + 1) ((gridCellEquiv (n + 1)).symm j) = j.val := by
      rw [← gridCellEquiv_val, Equiv.apply_symm_apply]
    rw [hj, Equiv.apply_symm_apply]
    apply (ZMod.val_natCast_of_lt ?_).symm
    have hlt : j.val < 2 ^ n * 2 := (ZMod.val_lt j).trans_eq (pow_succ 2 n)
    omega
  rw [harray]
  have hrefine := CircleStep.circleStep_refine_of_eq (2 ^ n) 2 (2 ^ (n + 1)) (pow_succ 2 n)
    (fun j => normalizedColumn n i ((gridCellEquiv n).symm j))
  exact congrFun hrefine x

def leafChild : (n : ℕ) → Grid n → Bool → Grid (n + 1)
  | 0, _, false => Sum.inl ()
  | 0, _, true => Sum.inr ()
  | n + 1, Sum.inl x, b => Sum.inl (leafChild n x b)
  | n + 1, Sum.inr x, b => Sum.inr (leafChild n x b)

theorem leafChild_ordinal (n : ℕ) (x : Grid n) (b : Bool) :
    gridOrdinal (n + 1) (leafChild n x b) = 2 * gridOrdinal n x + (if b then 1 else 0) := by
  induction n with
  | zero => cases x; cases b <;> rfl
  | succ n ih =>
    rcases x with x | x
    · rw [leafChild, gridOrdinal_left, gridOrdinal_left, ih]
    · rw [leafChild, gridOrdinal_right, gridOrdinal_right, ih, pow_succ]
      ring

theorem detailColumn_finest_pair (n : ℕ) (i : DetailIndex (n + 1))
    (hi : detailLevel (n + 1) i = n + 1) (x : Grid n) :
    detailColumn (n + 1) (fun _ => 1) i (leafChild n x false) +
      detailColumn (n + 1) (fun _ => 1) i (leafChild n x true) = 0 := by
  induction n with
  | zero =>
    rcases i with ⟨⟩ | (i | i)
    · cases x
      simp only [leafChild, detailColumn, Sum.elim_inl, Sum.elim_inr]
      rw [uniformRoot_left, uniformRoot_right, add_neg_cancel]
    · exact Empty.elim i
    · exact Empty.elim i
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i)
    · simp only [detailLevel] at hi
      omega
    · have hi' : detailLevel (n + 1) i = n + 1 := by simpa only [detailLevel, Nat.add_right_cancel_iff] using hi
      rcases x with x | x
      · simpa only [leafChild, detailColumn, Sum.elim_inl] using ih i hi' x
      · simp only [leafChild, detailColumn, Sum.elim_inr, add_zero]
    · have hi' : detailLevel (n + 1) i = n + 1 := by simpa only [detailLevel, Nat.add_right_cancel_iff] using hi
      rcases x with x | x
      · simp only [leafChild, detailColumn, Sum.elim_inl, add_zero]
      · simpa only [leafChild, detailColumn, Sum.elim_inr] using ih i hi' x

theorem normalizedColumn_finest_pair (n : ℕ) (i : Option (DetailIndex (n + 1)))
    (hi : modeLevel (n + 1) i = n + 1) (x : Grid n) :
    normalizedColumn (n + 1) i (leafChild n x true) =
      -normalizedColumn (n + 1) i (leafChild n x false) := by
  cases i with
  | none => simp only [modeLevel] at hi; omega
  | some i =>
    have hp := detailColumn_finest_pair n i hi x
    dsimp only [normalizedColumn, haarColumn]
    have heq : detailColumn (n + 1) (fun _ => 1) i (leafChild n x true) =
        -detailColumn (n + 1) (fun _ => 1) i (leafChild n x false) := by linarith
    rw [heq]
    ring

theorem paired_vector_representation (N : ℕ) [NeZero N] (v : ZMod (2 * N) → ℝ)
    (hv : ∀ j : ZMod N, v (((2 * j.val + 1 : ℕ) : ZMod (2 * N))) =
      -v (((2 * j.val : ℕ) : ZMod (2 * N)))) :
    v = dyadicDetailVector N (fun j => v (((2 * j.val : ℕ) : ZMod (2 * N)))) := by
  funext i
  let j : ZMod N := ((i.val / 2 : ℕ) : ZMod N)
  have hi := ZMod.val_lt i
  have hjlt : i.val / 2 < N := by omega
  have hj : j.val = i.val / 2 := ZMod.val_natCast_of_lt hjlt
  by_cases heven : i.val % 2 = 0
  · have heq : i = (((2 * j.val : ℕ) : ZMod (2 * N))) := by
      rw [hj]
      have hh : 2 * (i.val / 2) = i.val := by omega
      rw [hh, ZMod.natCast_zmod_val]
    rw [heq, dyadicDetailVector_left]
  · have heq : i = (((2 * j.val + 1 : ℕ) : ZMod (2 * N))) := by
      rw [hj]
      have hh : 2 * (i.val / 2) + 1 = i.val := by omega
      rw [hh, ZMod.natCast_zmod_val]
    rw [heq, dyadicDetailVector_right, hv]

theorem ordinaryColumn_finest_mem (n : ℕ) (i : Option (DetailIndex (n + 1)))
    (hi : modeLevel (n + 1) i = n + 1) : ordinaryColumn (n + 1) i ∈ detailSpace (2 ^ n) := by
  let v : ZMod (2 * 2 ^ n) → ℝ := fun j =>
    normalizedColumn (n + 1) i ((gridCellEquiv (n + 1)).symm
      ((j.val : ℕ) : ZMod (2 ^ (n + 1))))
  have hp : ∀ j : ZMod (2 ^ n), v (((2 * j.val + 1 : ℕ) : ZMod (2 * 2 ^ n))) =
      -v (((2 * j.val : ℕ) : ZMod (2 * 2 ^ n))) := by
    intro j
    have hj := ZMod.val_lt j
    have heven : 2 * j.val < 2 * 2 ^ n := by omega
    have hodd : 2 * j.val + 1 < 2 * 2 ^ n := by omega
    dsimp only [v]
    rw [ZMod.val_natCast_of_lt hodd, ZMod.val_natCast_of_lt heven]
    have hchild (b : Bool) : (gridCellEquiv (n + 1)).symm
        (((2 * j.val + (if b then 1 else 0) : ℕ) : ZMod (2 ^ (n + 1)))) =
        leafChild n ((gridCellEquiv n).symm j) b := by
      apply (gridCellEquiv (n + 1)).injective
      apply ZMod.val_injective
      rw [Equiv.apply_symm_apply, gridCellEquiv_val, leafChild_ordinal]
      have hjval : gridOrdinal n ((gridCellEquiv n).symm j) = j.val := by
        rw [← gridCellEquiv_val, Equiv.apply_symm_apply]
      rw [hjval]
      apply ZMod.val_natCast_of_lt
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact heven.trans_eq (by rw [pow_succ]; omega)
      · exact hodd.trans_eq (by rw [pow_succ]; omega)
    rw [show (2 * j.val + 1 : ℕ) = 2 * j.val + (if true then 1 else 0) by rfl,
      hchild true, show (2 * j.val : ℕ) = 2 * j.val + (if false then 1 else 0) by simp,
      hchild false]
    exact normalizedColumn_finest_pair n i hi _
  have hv := paired_vector_representation (2 ^ n) v hp
  let a : ZMod (2 ^ n) → ℝ := fun j => v (((2 * j.val : ℕ) : ZMod (2 * 2 ^ n)))
  refine ⟨a, ?_⟩
  change stepLp (2 * 2 ^ n) (dyadicDetailVector (2 ^ n) a) = ordinaryColumn (n + 1) i
  rw [← hv]
  have hcount : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; omega
  subst v
  subst a
  unfold ordinaryColumn
  have heq : ∀ (K : ℕ) [NeZero K] (hK : K = 2 ^ (n + 1)),
      stepLp K (fun j => normalizedColumn (n + 1) i ((gridCellEquiv (n + 1)).symm
        ((j.val : ℕ) : ZMod (2 ^ (n + 1))))) =
      stepLp (2 ^ (n + 1)) (fun j => normalizedColumn (n + 1) i ((gridCellEquiv (n + 1)).symm j)) := by
    intro K hKinst hK
    subst K
    simp only [ZMod.natCast_zmod_val]
  exact heq _ hcount

theorem detailLevel_le (n : ℕ) (i : DetailIndex n) : detailLevel n i ≤ n := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with _ | (i | i)
    · simp only [detailLevel]; omega
    · simp only [detailLevel]; exact Nat.add_le_add_right (ih i) 1
    · simp only [detailLevel]; exact Nat.add_le_add_right (ih i) 1

theorem detailEmbed_level (n : ℕ) (i : DetailIndex n) :
    detailLevel (n + 1) (detailEmbed n i) = detailLevel n i := by
  induction n with
  | zero => exact Empty.elim i
  | succ n ih =>
    rcases i with _ | (i | i) <;> simp only [detailEmbed, detailLevel]
    · rw [ih]
    · rw [ih]

theorem modeEmbed_level (n : ℕ) (i : Option (DetailIndex n)) :
    modeLevel (n + 1) (modeEmbed n i) = modeLevel n i := by
  cases i with
  | none => rfl
  | some i => exact detailEmbed_level n i

theorem detailEmbed_older (n : ℕ) (i : DetailIndex (n + 1)) (hi : detailLevel (n + 1) i ≤ n) :
    ∃ j : DetailIndex n, detailEmbed n j = i := by
  induction n with
  | zero =>
    have hp := detailLevel_pos 1 i
    change detailLevel 1 i ≤ 0 at hi
    omega
  | succ n ih =>
    rcases i with ⟨⟩ | (i | i)
    · exact ⟨Sum.inl (), rfl⟩
    · obtain ⟨j, hj⟩ := ih i (by simpa only [detailLevel, Nat.add_le_add_iff_right] using hi)
      exact ⟨Sum.inr (Sum.inl j), by simp only [detailEmbed, hj]; rfl⟩
    · obtain ⟨j, hj⟩ := ih i (by simpa only [detailLevel, Nat.add_le_add_iff_right] using hi)
      exact ⟨Sum.inr (Sum.inr j), by simp only [detailEmbed, hj]; rfl⟩

theorem modeEmbed_older (n : ℕ) (i : Option (DetailIndex (n + 1))) (hi : modeLevel (n + 1) i ≤ n) :
    ∃ j : Option (DetailIndex n), modeEmbed n j = i := by
  cases i with
  | none => exact ⟨none, rfl⟩
  | some i =>
    obtain ⟨j, hj⟩ := detailEmbed_older n i hi
    exact ⟨some j, by simp only [modeEmbed, hj]⟩

/-- Every finite-grid Haar column at generation `k+1` belongs to the same
literal circle detail space, independently of the fine grid resolution. -/
theorem ordinaryColumn_generation_mem (n k : ℕ) (i : Option (DetailIndex n))
    (hi : modeLevel n i = k + 1) : ordinaryColumn n i ∈ detailSpace (2 ^ k) := by
  induction n with
  | zero => cases i with
    | none => simp only [modeLevel] at hi; omega
    | some i => exact Empty.elim i
  | succ n ih =>
    by_cases hk : k = n
    · subst k
      exact ordinaryColumn_finest_mem n i hi
    · have hile : modeLevel (n + 1) i ≤ n + 1 := by
        cases i with
        | none => exact Nat.zero_le _
        | some i => exact detailLevel_le _ i
      have hiold : modeLevel (n + 1) i ≤ n := by omega
      obtain ⟨j, rfl⟩ := modeEmbed_older n i hiold
      rw [ordinaryColumn_refine]
      exact ih j (by rw [← modeEmbed_level]; exact hi)

theorem referenceSynthesis_add (n : ℕ) (x y : Option (DetailIndex n) → ℝ) :
    referenceSynthesis n (x + y) = referenceSynthesis n x + referenceSynthesis n y := by
  unfold referenceSynthesis
  rw [← stepLp_add]
  apply congrArg (stepLp (2 ^ n))
  funext j
  simp only [Matrix.mulVec_add, Pi.add_apply, mul_add]

theorem referenceSynthesis_smul (n : ℕ) (c : ℝ) (x : Option (DetailIndex n) → ℝ) :
    referenceSynthesis n (c • x) = c • referenceSynthesis n x := by
  unfold referenceSynthesis
  rw [← stepLp_smul]
  apply congrArg (stepLp (2 ^ n))
  funext j
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
  ring

def referenceSynthesisLinear (n : ℕ) : (Option (DetailIndex n) → ℝ) →ₗ[ℝ] CircleL2 where
  toFun := referenceSynthesis n
  map_add' := referenceSynthesis_add n
  map_smul' := fun c x => by rw [referenceSynthesis_smul]; rfl

theorem referenceSynthesis_single (n : ℕ) (i : Option (DetailIndex n)) (c : ℝ) :
    referenceSynthesis n (Pi.single i c) = c • ordinaryColumn n i := by
  unfold referenceSynthesis ordinaryColumn
  rw [← stepLp_smul]
  apply congrArg (stepLp (2 ^ n))
  funext j
  rw [Matrix.mulVec_single]
  dsimp only [normalizedColumn, Pi.smul_apply, smul_eq_mul]
  change Real.sqrt _ * (haarColumn _ _ _ _ * c) = c * (Real.sqrt _ * haarColumn _ _ _ _)
  ring

theorem referenceSynthesis_sum_columns (n : ℕ) (x : Option (DetailIndex n) → ℝ) :
    referenceSynthesis n x = ∑ i : Option (DetailIndex n), x i • ordinaryColumn n i := by
  have hx := Finset.univ_sum_single x
  have hm := map_sum (referenceSynthesisLinear n) (fun i => Pi.single i (x i)) Finset.univ
  change referenceSynthesis n (∑ i, Pi.single i (x i)) = ∑ i, referenceSynthesis n (Pi.single i (x i)) at hm
  rw [hx] at hm
  simpa only [referenceSynthesis_single] using hm

def generationCoordinates (n k : ℕ) (x : Option (DetailIndex n) → ℝ) : Option (DetailIndex n) → ℝ :=
  fun i => if modeLevel n i = k + 1 then x i else 0

def generationSynthesis (n k : ℕ) (x : Option (DetailIndex n) → ℝ) : CircleL2 :=
  referenceSynthesis n (generationCoordinates n k x)

theorem generationSynthesis_mem (n k : ℕ) (x : Option (DetailIndex n) → ℝ) :
    generationSynthesis n k x ∈ detailSpace (2 ^ k) := by
  rw [generationSynthesis, referenceSynthesis_sum_columns]
  apply Submodule.sum_mem
  intro i hi
  by_cases hlevel : modeLevel n i = k + 1
  · exact Submodule.smul_mem _ _ (ordinaryColumn_generation_mem n k i hlevel)
  · simp only [generationCoordinates, ite_eq_right hlevel, zero_smul, Submodule.zero_mem]

theorem generationSynthesis_norm_sq (n k : ℕ) (x : Option (DetailIndex n) → ℝ) :
    ‖generationSynthesis n k x‖ ^ 2 =
      ∑ i : Option (DetailIndex n), if modeLevel n i = k + 1 then (x i) ^ 2 else 0 := by
  rw [generationSynthesis, referenceSynthesis_norm_sq]
  unfold FiniteTransport.vectorSq generationCoordinates
  apply sum_congr rfl
  intro i hi
  split_ifs <;> simp

theorem massive_heat_generationSynthesis {t κ Λ ρ : ℝ} (ht : 0 < t)
    (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1 / 2)
    (n k : ℕ) (x : Option (DetailIndex n) → ℝ) :
    weightedFourierSq (massiveWeight κ Λ ρ) (heat t (generationSynthesis n k x)) ≤
      inverseConstant κ ρ * (Λ + ((2 * 2 ^ k : ℕ) : ℝ) ^ 2) ^ ρ *
        min 1 (((2 * 2 ^ k : ℕ) : ℝ)⁻¹ ^ 2 / (4 * t)) * ‖generationSynthesis n k x‖ ^ 2 := by
  have hmem := generationSynthesis_mem n k x
  have heq : detailProjection (2 ^ k) (generationSynthesis n k x) = generationSynthesis n k x :=
    (Submodule.starProjection_eq_self_iff).mpr hmem
  have hh := massive_heat_detailProjection ht hκ hΛ hρ hρhalf (2 ^ k) (generationSynthesis n k x)
  rw [heq] at hh
  exact hh

theorem leafParent_child (n : ℕ) (x : Grid n) (b : Bool) : leafParent n (leafChild n x b) = x := by
  induction n with
  | zero => cases x; cases b <;> rfl
  | succ n ih => rcases x with x | x <;> simp only [leafChild, leafParent, ih]

theorem sum_leafChildren (n : ℕ) (f : Grid (n + 1) → ℝ) :
    (∑ y, f y) = ∑ x, (f (leafChild n x false) + f (leafChild n x true)) := by
  induction n with
  | zero =>
    dsimp only [Grid, gridFintype]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, leafChild]
  | succ n ih =>
    calc
      _ = (∑ y : Grid (n + 1), f (Sum.inl y)) + ∑ y : Grid (n + 1), f (Sum.inr y) :=
        Fintype.sum_sum_type f
      _ = (∑ x : Grid n, (f (Sum.inl (leafChild n x false)) + f (Sum.inl (leafChild n x true)))) +
          ∑ x : Grid n, (f (Sum.inr (leafChild n x false)) + f (Sum.inr (leafChild n x true))) := by
        rw [ih (fun x => f (Sum.inl x)), ih (fun x => f (Sum.inr x))]
      _ = _ := (Fintype.sum_sum_type (fun x =>
        f (leafChild (n + 1) x false) + f (leafChild (n + 1) x true))).symm

def parentAverage (n : ℕ) (f : Grid (n + 1) → ℝ) (x : Grid n) : ℝ :=
  (f (leafChild n x false) + f (leafChild n x true)) / 2

theorem parentAverage_pullback (n : ℕ) (f : Grid n → ℝ) :
    parentAverage n (fun y => f (leafParent n y)) = f := by
  funext x
  rw [parentAverage, leafParent_child, leafParent_child]
  ring

def ordinaryCovarianceEntry (n : ℕ) (f : Grid n → ℝ)
    (i j : Option (DetailIndex n)) : ℝ :=
  ∑ x, f x * haarColumn n (fun _ => 1) i x * haarColumn n (fun _ => 1) j x

/-- Multiplication compressed to older Haar columns sees exactly the average
of each pair of child cells. This is an identity for arbitrary signed data. -/
theorem ordinaryCovarianceEntry_parent (n : ℕ) (f : Grid (n + 1) → ℝ)
    (i j : Option (DetailIndex n)) :
    ordinaryCovarianceEntry (n + 1) f (modeEmbed n i) (modeEmbed n j) =
      ordinaryCovarianceEntry n (parentAverage n f) i j := by
  rw [ordinaryCovarianceEntry]
  erw [sum_leafChildren n]
  unfold ordinaryCovarianceEntry
  apply sum_congr rfl
  intro x hx
  simp_rw [haarColumn_refine, leafParent_child]
  have hs : ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  calc
    _ = (f (leafChild n x false) + f (leafChild n x true)) * ((Real.sqrt 2)⁻¹) ^ 2 *
        haarColumn n (fun _ => 1) i x * haarColumn n (fun _ => 1) j x := by ring
    _ = _ := by rw [hs]; unfold parentAverage; ring

/-- The finite conditional average onto the dyadic generation prefix. It
retains every fine value when the requested prefix already fills the grid. -/
def coarseAverage : (n : ℕ) → ℕ → (Grid n → ℝ) → Grid n → ℝ
  | 0, _, f => f
  | n + 1, k, f => if n + 1 ≤ k then f
      else fun y => coarseAverage n k (parentAverage n f) (leafParent n y)

theorem coarseAverage_bounds (n k : ℕ) (f : Grid n → ℝ) (m U : ℝ)
    (hf : ∀ x, m ≤ f x ∧ f x ≤ U) :
    ∀ x, m ≤ coarseAverage n k f x ∧ coarseAverage n k f x ≤ U := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    unfold coarseAverage
    split_ifs
    · exact hf
    · have havg : ∀ x, m ≤ parentAverage n f x ∧ parentAverage n f x ≤ U := by
        intro x
        unfold parentAverage
        constructor <;> linarith [(hf (leafChild n x false)).1, (hf (leafChild n x false)).2,
          (hf (leafChild n x true)).1, (hf (leafChild n x true)).2]
      intro x
      exact ih _ havg (leafParent n x)

/-- Every actual coarse-prefix covariance entry depends only on the
corresponding dyadic conditional averages of the signed coefficient. -/
theorem ordinaryCovarianceEntry_coarseAverage (n k : ℕ) (f : Grid n → ℝ)
    (i j : Option (DetailIndex n)) (hi : modeLevel n i ≤ k) (hj : modeLevel n j ≤ k) :
    ordinaryCovarianceEntry n f i j = ordinaryCovarianceEntry n (coarseAverage n k f) i j := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hk : n + 1 ≤ k
    · rw [coarseAverage, ite_eq_left hk]
    · obtain ⟨i0, rfl⟩ := modeEmbed_older n i (by omega)
      obtain ⟨j0, rfl⟩ := modeEmbed_older n j (by omega)
      rw [ordinaryCovarianceEntry_parent, ordinaryCovarianceEntry_parent]
      rw [coarseAverage, ite_eq_right hk, parentAverage_pullback]
      apply ih
      · simpa only [modeEmbed_level] using hi
      · simpa only [modeEmbed_level] using hj

theorem ordinaryCovarianceEntry_matrix (n : ℕ) (f : Grid n → ℝ)
    (i j : Option (DetailIndex n)) :
    ((haarMatrix n (fun _ => 1))ᵀ * Matrix.diagonal f * haarMatrix n (fun _ => 1)) i j =
      ordinaryCovarianceEntry n f i j := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, haarMatrix, ordinaryCovarianceEntry]
  apply sum_congr rfl
  intro x hx
  ring

theorem parentAverage_sub (n : ℕ) (f g : Grid (n + 1) → ℝ) :
    parentAverage n (f - g) = parentAverage n f - parentAverage n g := by
  funext x
  dsimp only [parentAverage, Pi.sub_apply]
  ring

theorem coarseAverage_sub (n k : ℕ) (f g : Grid n → ℝ) :
    coarseAverage n k (f - g) = coarseAverage n k f - coarseAverage n k g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold coarseAverage
    split_ifs
    · rfl
    · rw [parentAverage_sub, ih]
      rfl

theorem sum_parent_pullback (n : ℕ) (f : Grid (n + 1) → ℝ) (g : Grid n → ℝ) :
    (∑ y, f y * g (leafParent n y)) = 2 * ∑ x, parentAverage n f x * g x := by
  erw [sum_leafChildren n]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x hx
  simp only [leafParent_child, parentAverage]
  ring

theorem sum_pullback_sq (n : ℕ) (g : Grid n → ℝ) :
    (∑ y : Grid (n + 1), (g (leafParent n y)) ^ 2) = 2 * ∑ x : Grid n, (g x) ^ 2 := by
  erw [sum_leafChildren n]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [leafParent_child, leafParent_child]
  ring

/-- The averaging identity needed for negative-norm input duality. -/
theorem coarseAverage_pairing (n k : ℕ) (f : Grid n → ℝ) :
    (∑ x, f x * coarseAverage n k f x) = ∑ x, (coarseAverage n k f x) ^ 2 := by
  induction n with
  | zero =>
    change (∑ x, f x * f x) = ∑ x, (f x) ^ 2
    apply sum_congr rfl
    intro x hx
    ring
  | succ n ih =>
    unfold coarseAverage
    split_ifs
    · apply sum_congr rfl; intro x hx; ring
    · dsimp only
      erw [sum_parent_pullback, sum_pullback_sq]
      rw [ih]

def gridStep (n : ℕ) (f : Grid n → ℝ) : CircleL2 :=
  stepLp (2 ^ n) (fun j => f ((gridCellEquiv n).symm j))

theorem gridStep_norm_sq (n : ℕ) (f : Grid n → ℝ) :
    ‖gridStep n f‖ ^ 2 = (((2 ^ n : ℕ) : ℝ))⁻¹ * ∑ x, (f x) ^ 2 := by
  rw [gridStep, stepLp_norm_sq]
  congr 1
  exact Equiv.sum_comp (gridCellEquiv n).symm (fun x => (f x) ^ 2)

theorem gridStep_add (n : ℕ) (f g : Grid n → ℝ) : gridStep n (f + g) = gridStep n f + gridStep n g := by
  unfold gridStep
  rw [← stepLp_add]
  rfl

theorem gridStep_sub (n : ℕ) (f g : Grid n → ℝ) : gridStep n (f - g) = gridStep n f - gridStep n g := by
  unfold gridStep
  rw [← stepLp_sub]
  rfl

theorem gridStep_inner (n : ℕ) (f g : Grid n → ℝ) :
    (inner ℂ (gridStep n f) (gridStep n g)).re =
      (((2 ^ n : ℕ) : ℝ))⁻¹ * ∑ x, f x * g x := by
  have hh := norm_add_sq (𝕜 := ℂ) (gridStep n f) (gridStep n g)
  rw [← gridStep_add, gridStep_norm_sq, gridStep_norm_sq, gridStep_norm_sq] at hh
  have hsum : (∑ x, ((f + g) x) ^ 2) =
      (∑ x, (f x) ^ 2) + 2 * (∑ x, f x * g x) + ∑ x, (g x) ^ 2 := by
    rw [Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    dsimp only [Pi.add_apply]
    ring
  rw [hsum] at hh
  change RCLike.re (inner ℂ (gridStep n f) (gridStep n g)) = _
  linarith

theorem gridStep_coarseAverage_pairing (n k : ℕ) (f : Grid n → ℝ) :
    (inner ℂ (gridStep n f) (gridStep n (coarseAverage n k f))).re =
      ‖gridStep n (coarseAverage n k f)‖ ^ 2 := by
  rw [gridStep_inner, gridStep_norm_sq, coarseAverage_pairing]

theorem leafParent_cell (n : ℕ) (j : ZMod (2 ^ (n + 1))) :
    leafParent n ((gridCellEquiv (n + 1)).symm j) =
      (gridCellEquiv n).symm (((j.val / 2 : ℕ) : ZMod (2 ^ n))) := by
  apply (gridCellEquiv n).injective
  apply ZMod.val_injective
  rw [gridCellEquiv_val, leafParent_ordinal]
  have hj : gridOrdinal (n + 1) ((gridCellEquiv (n + 1)).symm j) = j.val := by
    rw [← gridCellEquiv_val, Equiv.apply_symm_apply]
  rw [hj, Equiv.apply_symm_apply]
  apply (ZMod.val_natCast_of_lt ?_).symm
  have hlt : j.val < 2 ^ n * 2 := (ZMod.val_lt j).trans_eq (pow_succ 2 n)
  omega

theorem gridStep_parent (n : ℕ) (f : Grid n → ℝ) :
    gridStep (n + 1) (fun y => f (leafParent n y)) = gridStep n f := by
  unfold gridStep
  have harray : (fun j : ZMod (2 ^ (n + 1)) => f (leafParent n ((gridCellEquiv (n + 1)).symm j))) =
      (fun j => f ((gridCellEquiv n).symm (((j.val / 2 : ℕ) : ZMod (2 ^ n))))) := by
    funext j
    rw [leafParent_cell]
  rw [harray]
  apply Lp.ext
  have hleft := stepLp_ae (2 ^ (n + 1))
    (fun j => f ((gridCellEquiv n).symm (((j.val / 2 : ℕ) : ZMod (2 ^ n)))))
  have hright := stepLp_ae (2 ^ n) (fun j => f ((gridCellEquiv n).symm j))
  apply hleft.trans
  apply Filter.EventuallyEq.trans _ hright.symm
  have heq := CircleStep.circleStep_refine_of_eq (2 ^ n) 2 (2 ^ (n + 1)) (pow_succ 2 n)
    (fun j => f ((gridCellEquiv n).symm j))
  exact ae_of_all _ (fun x => congrFun heq x)

/-- The actual averaged coefficient is a literal stepfield at the coarse
resolution, even when the original coefficient lives on an arbitrarily
fine grid. -/
theorem gridStep_coarseAverage_witness (n k : ℕ) (hk : k ≤ n) (f : Grid n → ℝ) :
    ∃ v : ZMod (2 ^ k) → ℝ, gridStep n (coarseAverage n k f) = stepLp (2 ^ k) v := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst k
    exact ⟨fun j => f ((gridCellEquiv 0).symm j), rfl⟩
  | succ n ih =>
    by_cases hkfull : n + 1 ≤ k
    · have heq : k = n + 1 := by omega
      subst k
      rw [coarseAverage, ite_eq_left le_rfl]
      exact ⟨fun j => f ((gridCellEquiv (n + 1)).symm j), rfl⟩
    · rw [coarseAverage, ite_eq_right hkfull, gridStep_parent]
      exact ih (by omega) (parentAverage n f)

end FiniteHaar
end SHE
