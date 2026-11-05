module

public import SHEStochastic.MatrixPointHeatRows
public import SHEStochastic.RealCausalHeatKernel
public import SHEStochastic.HolderWeightedEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixPointRowDomination
open MeasureTheory SHE SHE.StoppedFourier SHE.FiniteHaar SHE.DyadicApproximation MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Literal scalar heat tests are the causal physical real kernels,
including zero and negative ages. -/
theorem scalar_test_ae (τ : ℝ) (x : HeatCircle) :
    ScalarHaarHeatRows.test τ x =ᵐ[ν] fun y =>
      RealCausalHeatKernel.value x τ (CircleNormalization.scale 1 (2*Real.pi) y) := by
  by_cases ht : 0 < τ
  · filter_upwards [VectorPointHeatTest.scalar_ae ht x] with y hy
    rw [hy]
    simp only [RealCausalHeatKernel.value,dif_pos ht,ContinuousMap.coe_mk,NativeHeatSpan.kernel_eq_physical]
  · have hz : ScalarHaarHeatRows.test τ x = 0 := by
      simp only [ScalarHaarHeatRows.test,circleHeat,dif_neg ht,map_zero]
      change (Complex.reCLM.compLpL 2 ν) 0 = 0
      rw [map_zero]
    rw [hz]
    have hzero : ∀ᵐ y ∂ν, (0 : RealL2) y = (0 : ℝ) := by
      simpa using (Lp.coeFn_zero ℝ 2 ν)
    filter_upwards [hzero] with y hy
    rw [hy,RealCausalHeatKernel.nonpos (not_lt.mp ht)]
    rfl

theorem test_ae (τ : ℝ) (x : HeatCircle) (i : d) :
    VectorPointHeatTest.test τ x i =ᵐ[ν] fun y =>
      RealCausalHeatKernel.value x τ (CircleNormalization.scale 1 (2*Real.pi) y) •
        EuclideanSpace.single i (1 : ℝ) := by
  filter_upwards [(L2EuclideanCoordinates.injection i).coeFn_compLpL (ScalarHaarHeatRows.test τ x),
    scalar_test_ae τ x] with y hy hs
  change (L2EuclideanCoordinates.injection i).compLpL 2 ν (ScalarHaarHeatRows.test τ x) y = _
  rw [hy,hs]
  rfl

/-- The vector feature energy is exactly the scalar physical kernel
energy, with no dimension factor and the original circle normalization. -/
theorem test_difference_energy (τ σ : ℝ) (x y : HeatCircle) (i : d) :
    ENNReal.ofReal (‖VectorPointHeatTest.test τ x i-VectorPointHeatTest.test σ y i‖^2) =
      ∫⁻ z : HeatCircle, ENNReal.ofReal
        ((RealCausalHeatKernel.value x τ z-RealCausalHeatKernel.value y σ z)^2)
          ∂AddCircle.haarAddCircle := by
  rw [← HolderWeightedEnergy.state_mass]
  calc
    _ = ∫⁻ z, ENNReal.ofReal
        ((RealCausalHeatKernel.value x τ (CircleNormalization.scale 1 (2*Real.pi) z)-
          RealCausalHeatKernel.value y σ (CircleNormalization.scale 1 (2*Real.pi) z))^2) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (VectorPointHeatTest.test τ x i) (VectorPointHeatTest.test σ y i),
        test_ae τ x i,test_ae σ y i] with z hs hx hy
      rw [hs]
      change ENNReal.ofReal (‖VectorPointHeatTest.test τ x i z-VectorPointHeatTest.test σ y i z‖^2) = _
      rw [hx,hy,← sub_smul,norm_smul]
      simp only [PiLp.norm_single,Real.norm_eq_abs,abs_one,mul_one,sq_abs]
    _ = _ := (CircleNormalization.scale_measurePreserving 1 (2*Real.pi)).lintegral_comp_emb
      (CircleNormalization.scaleMeasurableEquiv 1 (2*Real.pi)).measurableEmbedding
      (fun z : HeatCircle => ENNReal.ofReal ((RealCausalHeatKernel.value x τ z-RealCausalHeatKernel.value y σ z)^2))

/-- Covariance bounds dominate the full actual Haar row difference by
the scalar heat geometry. The covariance field may be random and coupled. -/
theorem bound (P : Profile d) (τ σ : ℝ) (x y : HeatCircle) (i : d)
    {U : ℝ} (hU : P.upper ≤ U) :
    ENNReal.ofReal (‖MatrixPointHeatRows.row τ P x i-MatrixPointHeatRows.row σ P y i‖^2) ≤
      ENNReal.ofReal U * (∫⁻ z : HeatCircle, ENNReal.ofReal
        ((RealCausalHeatKernel.value x τ z-RealCausalHeatKernel.value y σ z)^2)
          ∂AddCircle.haarAddCircle) := by
  rw [← test_difference_energy τ σ x y i,← ENNReal.ofReal_mul (P.upper_pos.le.trans hU)]
  apply ENNReal.ofReal_le_ofReal
  rw [MatrixPointHeatRows.row_eq,MatrixPointHeatRows.row_eq,← map_sub]
  have he := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (factor P).adjoint
    (VectorPointHeatTest.test τ x i-VectorPointHeatTest.test σ y i)
  rw [ContinuousLinearMap.adjoint_adjoint,covariance] at he
  rw [he]
  exact (bounded P _).trans (mul_le_mul_of_nonneg_right hU (sq_nonneg _))

end SHEStochastic.MatrixPointRowDomination
