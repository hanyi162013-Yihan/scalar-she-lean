module

public import SHE.SignedTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CoarseCompression
open Matrix Finset FiniteTransport

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
theorem gram_vector_isometry (H : Matrix β α ℝ) (hH : Hᵀ*H=1) (x : α → ℝ) :
    vectorSq (H*ᵥx)=vectorSq x := by
  have hh := covariance_energy Hᵀ x
  rw [Matrix.transpose_transpose,hH,Matrix.one_mulVec] at hh
  simpa only [vectorSq,dotProduct,pow_two] using hh

omit [DecidableEq α] in
theorem gram_covariance_energy (H : Matrix β α ℝ) (c : β → ℝ) (x : α → ℝ) :
    x ⬝ᵥ ((Hᵀ*Matrix.diagonal c*H)*ᵥx) = ∑ y, c y*((H*ᵥx) y)^2 := by
  calc
    _ = x ⬝ᵥ (Hᵀ*ᵥ(Matrix.diagonal c*ᵥ(H*ᵥx))) := by
      rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _ = (Matrix.diagonal c*ᵥ(H*ᵥx)) ⬝ᵥ (H*ᵥx) := Matrix.dotProduct_transpose_mulVec _ _ _
    _ = _ := by
      simp only [dotProduct,Matrix.mulVec_diagonal]
      apply sum_congr rfl
      intro y hy
      ring

/-- A compressed multiplication covariance has a dimension-free signed
Frobenius estimate. The spatial cost is its actual Christoffel row mass. -/
theorem compressed_covariance_frobenius (H : Matrix β α ℝ)
    (hH : Hᵀ*H=1) (f : β → ℝ) (K : ℝ)
    (hrow : ∀ y, ∑ i, (H y i)^2 ≤ K) :
    frobeniusSq (Hᵀ*Matrix.diagonal f*H) ≤ K*∑ y, (f y)^2 := by
  have htrans : ∀ x : β → ℝ, vectorSq (Hᵀ*ᵥx) ≤ 1*vectorSq x :=
    transpose_vectorSq_le H 1 (by norm_num)
      (fun x => by rw [gram_vector_isometry H hH x]; simp)
  have hh := frobeniusSq_mul_le Hᵀ (Matrix.diagonal f*H) 1 htrans
  rw [← Matrix.mul_assoc,one_mul] at hh
  calc
    _ ≤ frobeniusSq (Matrix.diagonal f*H) := hh
    _ = ∑ y, (f y)^2 * ∑ i, (H y i)^2 := by
      simp only [frobeniusSq,Matrix.diagonal_mul,mul_pow,mul_sum]
    _ ≤ ∑ y, (f y)^2*K := sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hrow y) (sq_nonneg _)
    _ = _ := by rw [← sum_mul,mul_comm]

section Restriction
variable (p : α → Prop) [DecidablePred p]

def principal (T : Matrix α α ℝ) : Matrix {i // p i} {i // p i} ℝ :=
  fun i j => T i.val j.val

def columns (H : Matrix β α ℝ) : Matrix β {i // p i} ℝ := fun y i => H y i.val

omit [Fintype α] [DecidableEq β] [DecidablePred p] in
theorem columns_gram (H : Matrix β α ℝ) (hH : Hᵀ*H=1) :
    (columns p H)ᵀ*columns p H=1 := by
  ext i j
  have hh := congrFun (congrFun hH i.val) j.val
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,columns,Matrix.one_apply,
    Subtype.ext_iff] using hh

omit [DecidableEq α] in
theorem sum_subtype_of_zero (f : α → ℝ) (hzero : ∀ i, ¬p i → f i=0) :
    (∑ i : {i // p i}, f i.val) = ∑ i, f i := by
  have hh := Fintype.sum_subtype_add_sum_subtype p f
  have hz : (∑ i : {i // ¬p i}, f i.val)=0 := by
    apply sum_eq_zero
    intro i hi
    exact hzero i.val i.property
  simpa only [hz,add_zero] using hh

omit [DecidableEq α] in
/-- The actual zero block makes principal covariance compression exact. -/
theorem principal_covariance (T : Matrix α α ℝ)
    (hzero : ∀ i : {i // p i}, ∀ j, ¬p j → T i.val j=0) :
    principal p T*(principal p T)ᵀ = principal p (T*Tᵀ) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,principal]
  exact sum_subtype_of_zero p (fun k => T i.val k*T j.val k)
    (fun k hk => by rw [hzero i k hk,zero_mul])

omit [Fintype α] [DecidableEq α] [DecidablePred p] in
theorem principal_gram_covariance (H : Matrix β α ℝ) (c : β → ℝ) :
    principal p (Hᵀ*Matrix.diagonal c*H) = (columns p H)ᵀ*Matrix.diagonal c*columns p H := by
  ext i j
  simp only [principal,columns,Matrix.mul_apply,Matrix.transpose_apply]

omit [DecidableEq α] in
theorem principal_frobenius (L M : Matrix α α ℝ)
    (hLzero : ∀ i : {i // p i}, ∀ j, ¬p j → L i.val j=0)
    (hMzero : ∀ i : {i // p i}, ∀ j, ¬p j → M i.val j=0) :
    frobeniusSq (principal p L-principal p M) =
      ∑ i : {i // p i}, ∑ j : α, (L i.val j-M i.val j)^2 := by
  unfold frobeniusSq
  apply sum_congr rfl
  intro i hi
  exact sum_subtype_of_zero p (fun j => (L i.val j-M i.val j)^2)
    (fun j hj => by rw [hLzero i j hj,hMzero i j hj]; norm_num)

end Restriction

/-- Ellipticity of a compressed multiplication operator follows from
pointwise coefficient bounds and its true orthonormal columns. -/
theorem gram_covariance_bounds (H : Matrix β α ℝ) (hH : Hᵀ*H=1)
    (c : β → ℝ) (m U : ℝ) (hc : ∀ y, m ≤ c y ∧ c y ≤ U) (x : α → ℝ) :
    m*vectorSq x ≤ x ⬝ᵥ ((Hᵀ*Matrix.diagonal c*H)*ᵥx) ∧
      x ⬝ᵥ ((Hᵀ*Matrix.diagonal c*H)*ᵥx) ≤ U*vectorSq x := by
  rw [gram_covariance_energy]
  constructor
  · calc
      _ = m*vectorSq (H*ᵥx) := by rw [gram_vector_isometry H hH]
      _ = ∑ y, m*((H*ᵥx) y)^2 := by rw [vectorSq,mul_sum]
      _ ≤ _ := sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hc y).1 (sq_nonneg _)
  · calc
      _ ≤ ∑ y, U*((H*ᵥx) y)^2 :=
        sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hc y).2 (sq_nonneg _)
      _ = U*vectorSq (H*ᵥx) := by rw [vectorSq,mul_sum]
      _ = _ := by rw [gram_vector_isometry H hH]

/-- Uniform signed coarse-output prefix bound inside an arbitrary
finer resolution. Only the genuine vanishing block, orthonormal Haar
columns and their row mass are supplied by the spatial construction. -/
theorem signed_principal_frobenius [LinearOrder α]
    (p : α → Prop) [DecidablePred p]
    (H : Matrix β α ℝ) (hH : Hᵀ*H=1)
    (L M : Matrix α α ℝ) (c d : β → ℝ) (m U K : ℝ)
    (hm : 0 < m) (hU : 0 ≤ U)
    (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLp : ∀ i, 0 < L i i) (hMp : ∀ i, 0 < M i i)
    (hLc : L*Lᵀ=Hᵀ*Matrix.diagonal c*H)
    (hMd : M*Mᵀ=Hᵀ*Matrix.diagonal d*H)
    (hc : ∀ y, m ≤ c y ∧ c y ≤ U) (hd : ∀ y, m ≤ d y ∧ d y ≤ U)
    (hLzero : ∀ i : {i // p i}, ∀ j, ¬p j → L i.val j=0)
    (hMzero : ∀ i : {i // p i}, ∀ j, ¬p j → M i.val j=0)
    (hrow : ∀ y, ∑ i : {i // p i}, (H y i.val)^2 ≤ K) :
    (∑ i : {i // p i}, ∑ j : α, (L i.val j-M i.val j)^2) ≤
      U/m^2*K*∑ y, (c y-d y)^2 := by
  let HP := columns p H
  have hHP : HPᵀ*HP=1 := columns_gram p H hH
  have hLP : principal p L*(principal p L)ᵀ=HPᵀ*Matrix.diagonal c*HP := by
    rw [principal_covariance p L hLzero,hLc,principal_gram_covariance]
  have hMP : principal p M*(principal p M)ᵀ=HPᵀ*Matrix.diagonal d*HP := by
    rw [principal_covariance p M hMzero,hMd,principal_gram_covariance]
  have hLlower : (principal p L).IsLowerTriangular := fun i j hij => hL hij
  have hMlower : (principal p M).IsLowerTriangular := fun i j hij => hM hij
  have hh := cholesky_signed_frobeniusSq_of_covariance (principal p L) (principal p M) m U hm hU
    hLlower hMlower (fun i => hLp i.val) (fun i => hMp i.val)
    (fun x => by rw [hLP]; exact (gram_covariance_bounds HP hHP c m U hc x).2)
    (fun x => by rw [hLP]; exact (gram_covariance_bounds HP hHP c m U hc x).1)
    (fun x => by rw [hMP]; exact (gram_covariance_bounds HP hHP d m U hd x).1)
  have hdiff : principal p L*(principal p L)ᵀ-principal p M*(principal p M)ᵀ =
      HPᵀ*Matrix.diagonal (c-d)*HP := by
    rw [hLP,hMP,← Matrix.sub_mul,← Matrix.mul_sub,Matrix.diagonal_sub]
    rfl
  rw [principal_frobenius p L M hLzero hMzero,hdiff] at hh
  have hb := compressed_covariance_frobenius HP hHP (c-d) K hrow
  calc
    _ ≤ U/m^2*frobeniusSq (HPᵀ*Matrix.diagonal (c-d)*HP) := hh
    _ ≤ U/m^2*(K*∑ y, (c y-d y)^2) :=
      mul_le_mul_of_nonneg_left hb (div_nonneg hU (sq_nonneg m))
    _ = _ := by ring

end SHE.CoarseCompression

namespace SHE.CoarseCompression
open Matrix Finset FiniteTransport

theorem frobeniusSq_zero_iff {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) : frobeniusSq A=0 ↔ A=0 := by
  constructor
  · intro h
    ext i j
    have hi : (∑ k, (A i k)^2) ≤ frobeniusSq A :=
      Finset.single_le_sum (fun r _ => sum_nonneg (fun _ _ => sq_nonneg _)) (mem_univ i)
    have hj : (A i j)^2 ≤ ∑ k, (A i k)^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (mem_univ j)
    have hz : (A i j)^2=0 := le_antisymm (by linarith) (sq_nonneg _)
    simpa only [Matrix.zero_apply] using (sq_eq_zero_iff.mp hz)
  · intro h
    subst A
    simp [frobeniusSq]

/-- Positive triangular covariance factors are unique, including on
every actual principal block. No dimension-dependent norm or extra
ellipticity hypothesis is needed for this exact identity. -/
theorem triangular_covariance_unique {α : Type*} [Fintype α] [LinearOrder α]
    (L M : Matrix α α ℝ) (hL : L.IsLowerTriangular) (hM : M.IsLowerTriangular)
    (hLp : ∀ i, 0<L i i) (hMp : ∀ i, 0<M i i)
    (hcov : L*Lᵀ=M*Mᵀ) : L=M := by
  have hLd : IsUnit L.det := isUnit_iff_ne_zero.mpr
    ((hL.det_ne_zero_iff).mpr (fun i => (hLp i).ne'))
  have hMd : IsUnit M.det := isUnit_iff_ne_zero.mpr
    ((hM.det_ne_zero_iff).mpr (fun i => (hMp i).ne'))
  let : Invertible L := Matrix.invertibleOfIsUnitDet L hLd
  let : Invertible M := Matrix.invertibleOfIsUnitDet M hMd
  have hh := signed_covariance_frobeniusSq_le L M hL hM hLp hMp
  rw [hcov,sub_self,Matrix.mul_zero,Matrix.zero_mul] at hh
  have hz : frobeniusSq (L⁻¹*(L-M))=0 := by
    have hzero : frobeniusSq (0 : Matrix α α ℝ)=0 := by simp [frobeniusSq]
    rw [hzero] at hh
    exact le_antisymm hh (frobeniusSq_nonneg _)
  have hmat := (frobeniusSq_zero_iff _).mp hz
  have hm := congrArg (fun A : Matrix α α ℝ => L*A) hmat
  rw [Matrix.mul_inv_cancel_left_of_invertible,Matrix.mul_zero] at hm
  exact sub_eq_zero.mp hm

end SHE.CoarseCompression
