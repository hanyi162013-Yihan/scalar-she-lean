module

public import SHE.FiniteCovariancePullback
public import SHE.FiniteAffineDriftCancellation
public import SHE.FiniteItoNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.FiniteMappedGradient
open GaussianIncrement SmoothCylinders FiniteCovariancePullback
variable {m n : ℕ} {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

def contract (A : State n→L[ℝ]ℝ) (R : Fin n→C) : C :=
  ∑ i:Fin n,A (EuclideanSpace.basisFun (Fin n) ℝ i) • R i

theorem linear_basis (A : State n→L[ℝ]ℝ) (x : State n) :
    A x=∑ i:Fin n,x i*A (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  let e:=EuclideanSpace.basisFun (Fin n) ℝ
  have hx : (∑ i:Fin n,x i • e i)=x:=by simpa only [e,EuclideanSpace.basisFun_repr] using e.sum_repr x
  calc
    A x=A (∑ i:Fin n,x i • e i):=by rw [hx]
    _=∑ i:Fin n,x i*A (EuclideanSpace.basisFun (Fin n) ℝ i):=by
      simp only [map_sum,map_smul,smul_eq_mul,e]

/-- Gradient-noise pullback by a genuine finite linear observation,
retaining every shared-driver cross term. -/
theorem contract_comp (A : State n→L[ℝ]ℝ) (L : State m→L[ℝ]State n) (R : Fin m→C) :
    contract (A.comp L) R=contract A (mappedRow L R) := by
  calc
    _=∑ j:Fin m,(∑ i:Fin n,coefficient L i j*A (EuclideanSpace.basisFun (Fin n) ℝ i)) • R j:=by
      unfold contract
      apply Finset.sum_congr rfl
      intro j _
      rw [ContinuousLinearMap.comp_apply,linear_basis A]
      rfl
    _=∑ j:Fin m,∑ i:Fin n,A (EuclideanSpace.basisFun (Fin n) ℝ i) • (coefficient L i j • R j):=by
      simp only [Finset.sum_smul,smul_smul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _=∑ i:Fin n,∑ j:Fin m,A (EuclideanSpace.basisFun (Fin n) ℝ i) • (coefficient L i j • R j):=Finset.sum_comm
    _=_:=by simp only [contract,mappedRow,Finset.smul_sum]

theorem paired_gradient (L M : State m→L[ℝ]State n) {F : State n→ℝ}
    (hF : BoundedSmooth F) (z : State m) (R : Fin m→C) :
    contract (fderiv ℝ (fun w=>F (L w)-F (M w)) z) R=
      contract (fderiv ℝ F (L z)) (mappedRow L R)-contract (fderiv ℝ F (M z)) (mappedRow M R) := by
  have hl:=hF.smooth.differentiable (by simp)
  have hd : fderiv ℝ (fun w=>F (L w)-F (M w)) z=
      (fderiv ℝ F (L z)).comp L-(fderiv ℝ F (M z)).comp M := by
    exact (((hl (L z)).hasFDerivAt.comp z L.hasFDerivAt).sub
      ((hl (M z)).hasFDerivAt.comp z M.hasFDerivAt)).fderiv
  rw [hd]
  have he : contract ((fderiv ℝ F (L z)).comp L-(fderiv ℝ F (M z)).comp M) R=
      contract ((fderiv ℝ F (L z)).comp L) R-contract ((fderiv ℝ F (M z)).comp M) R := by
    simp only [contract,ContinuousLinearMap.sub_apply,sub_smul,Finset.sum_sub_distrib]
  rw [he,contract_comp,contract_comp]

/-- The complete comparison noise has BOTH the signed-row term and the
reference row multiplied by the gradient difference. -/
theorem complete (A B : State n→L[ℝ]ℝ) (R S : Fin n→C) :
    contract A R-contract B S=
      contract A (fun i=>R i-S i)+contract (A-B) S := by
  simp only [contract,ContinuousLinearMap.sub_apply,smul_sub,sub_smul,Finset.sum_sub_distrib]
  module

end SHE.FiniteMappedGradient
