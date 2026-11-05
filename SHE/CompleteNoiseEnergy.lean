module

public import SHE.FiniteMappedGradient
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.CompleteNoiseEnergy
open GaussianIncrement FiniteMappedGradient
variable {n : ℕ} {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Actual square-summable common-driver row energy controls the finite
noise contraction, without assuming independent observation rows. -/
theorem contract_bound (A : State n→L[ℝ]ℝ) (R : Fin n→C) :
    ‖contract A R‖^2≤(n:ℝ)*‖A‖^2*(∑ i:Fin n,‖R i‖^2) := by
  let e:=EuclideanSpace.basisFun (Fin n) ℝ
  have he (i:Fin n) : ‖e i‖=1:=e.orthonormal.norm_eq_one i
  have hi (i:Fin n) : ‖A (e i) • R i‖^2≤‖A‖^2*‖R i‖^2 := by
    have ha : ‖A (e i)‖≤‖A‖:=by simpa only [he i,mul_one] using A.le_opNorm (e i)
    rw [norm_smul,mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ha 2) (sq_nonneg _)
  calc
    _≤(∑ i:Fin n,‖A (e i) • R i‖)^2:=pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _≤(n:ℝ)*(∑ i:Fin n,‖A (e i) • R i‖^2):=by
      simpa only [Finset.card_univ,Fintype.card_fin] using
        (sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun i:Fin n=>‖A (e i) • R i‖))
    _≤(n:ℝ)*(∑ i:Fin n,‖A‖^2*‖R i‖^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>hi i)) (by positivity)
    _=_:=by rw [←Finset.mul_sum];ring

/-- BOTH complete first-Gamma terms contribute. The second term is
controlled by the actual gradient displacement and reference-row energy;
it cannot be discarded by centering the first signed-row term. -/
theorem complete_bound (A B : State n→L[ℝ]ℝ) (R S : Fin n→C) :
    ‖contract A R-contract B S‖^2≤
      2*(n:ℝ)*‖A‖^2*(∑ i:Fin n,‖R i-S i‖^2)+
      2*(n:ℝ)*‖A-B‖^2*(∑ i:Fin n,‖S i‖^2) := by
  rw [complete]
  have hn:=(pow_le_pow_left₀ (norm_nonneg _) (norm_add_le
    (contract A (fun i=>R i-S i)) (contract (A-B) S)) 2).trans
      (add_pow_le (norm_nonneg _) (norm_nonneg _) 2)
  norm_num only [Nat.reduceSub,pow_one] at hn
  have h1:=contract_bound A (fun i=>R i-S i)
  have h2:=contract_bound (A-B) S
  nlinarith

end SHE.CompleteNoiseEnergy
