module
public import SHE.CanonicalDefectCosts
public import SHE.StateBands
public import SHE.ScalarHeatBandBernstein
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.ActualGaussianMarkCoefficient
open Real Filter Topology
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall
variable (ell M:ℝ)(hell:0<ell)(hM:0≤M)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)(N:ℕ)(η:ℝ)

def constant:ℝ:=DefectGapFiniteCoefficient.constant Rough
  (ControlledOldIntervals.fraction Rough*(Rough).lower) (PhysicalScoreChain.uniformConstant 1)
  (ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta N) η N
  (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i Rough)

def coefficient(Λ:ℝ):ℝ:=sqrt (constant D hT hT1 hsmall ell M hell hM ρ hρ hρhalf N η)*
  DefectGapFiniteCoefficient.clock Λ ρ*StateBands.geometricConstant (D.beta-η)*Λ^(-(D.beta-η)/4)
local notation "C"=>constant D hT hT1 hsmall ell M hell hM ρ hρ hρhalf N η
local notation "a"=>coefficient D hT hT1 hsmall ell M hell hM ρ hρ hρhalf N η

private theorem geometric_nonneg{q:ℝ}(hq:0≤q):0≤StateBands.geometricConstant q:=by
  unfold StateBands.geometricConstant
  apply inv_nonneg.mpr
  have hh:=rpow_le_one_of_one_le_of_nonpos (by norm_num:(1:ℝ)≤2) (neg_nonpos.mpr hq)
  linarith

theorem cap(n:ℕ){Λ R:ℝ}(hΛ:1≤Λ)(hR:Λ^(1/4:ℝ)≤R)(hη:η<D.beta):
    sqrt (DefectGapFiniteCoefficient.constant (Smooth n)
      (ControlledOldIntervals.fraction (Smooth n)*(Smooth n).lower) (PhysicalScoreChain.uniformConstant 1)
      (ScalarHeatBandBernstein.amplitude D.cap D.holderConstant (Smooth n).exponent N) η N
      (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i (Smooth n)))*
      DefectGapFiniteCoefficient.clock Λ ρ*StateBands.geometricConstant ((Smooth n).exponent-η)*
      R^(-((Smooth n).exponent-η))≤a Λ:=by
  have hΛ0:0<Λ:=zero_lt_one.trans_le hΛ
  have hg:0<D.beta-η:=sub_pos.mpr hη
  have hp:=rpow_le_rpow_of_nonpos (rpow_pos_of_pos hΛ0 (1/4:ℝ)) hR (neg_nonpos.mpr hg.le)
  rw [←rpow_mul hΛ0.le] at hp
  have hp':R^(-(D.beta-η))≤Λ^(-(D.beta-η)/4):=by convert hp using 1 <;> congr 1 <;> ring
  have he:=CanonicalDefectCosts.finite_constant D hT hT1 hsmall ell M hell hM ρ hρ hρhalf n N
    (ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta N) η
  change sqrt _*DefectGapFiniteCoefficient.clock Λ ρ*StateBands.geometricConstant (D.beta-η)*R^(-(D.beta-η))≤_
  have hβeq:(Smooth n).exponent=D.beta:=rfl
  simp only [hβeq]
  rw [he]
  exact mul_le_mul_of_nonneg_left hp' (mul_nonneg
    (mul_nonneg (sqrt_nonneg _) (DefectGapFiniteCoefficient.clock_nonneg hΛ0.le hρ))
    (geometric_nonneg hg.le))

theorem nonneg{Λ:ℝ}(hΛ:0≤Λ)(hη:η<D.beta):0≤a Λ:=by
  unfold coefficient
  exact mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _)
    (DefectGapFiniteCoefficient.clock_nonneg hΛ hρ)) (geometric_nonneg (sub_nonneg.mpr hη.le))) (rpow_nonneg hΛ _)

theorem tends_zero(hη:η<D.beta):Tendsto a atTop (𝓝 0):=by
  have hh:=DefectGapFiniteCoefficient.rms_tends_zero Rough
    (ControlledOldIntervals.fraction Rough*(Rough).lower) (PhysicalScoreChain.uniformConstant 1)
    (ScalarHeatBandBernstein.amplitude D.cap D.holderConstant D.beta N) η ρ ((D.beta-η)/4) N
    (fun i=>ControlledDefectConstants.constant ell M hell hM ρ hρ hρhalf i Rough) hρ (by linarith)
  have ht:=hh.const_mul (StateBands.geometricConstant (D.beta-η))
  have he:a=(fun Λ:ℝ=>StateBands.geometricConstant (D.beta-η)*(sqrt C*DefectGapFiniteCoefficient.clock Λ ρ*Λ^(-(D.beta-η)/4))):=by
    funext Λ
    dsimp only [coefficient]
    ring
  rw [he]
  simpa only [mul_zero,constant,neg_div] using ht
end SHE.ActualGaussianMarkCoefficient
