module

public import SHE.NativeSignedClock
public import SHE.MixedDampedDifferenceEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.NativeSignedDamping
open Set MeasureTheory Real FiniteHaar NativeHeatObservation PredictableL2
open scoped NNReal ENNReal
local instance nativeSignedDamping_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeSignedDamping_sigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeSignedDamping_borel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeSignedDamping_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
variable {κ Λ ρ ell M:ℝ} (hκ:0≤κ) (hΛ:1≤Λ) (hρ:0<ρ) (hρ1:ρ<1/2)
variable (hell:0<ell) (hM:0≤M)

include hκ hΛ hρ hρ1 hM in
theorem point_bound (τ:ℝ) (f g:EllipticField ell M):
    ENNReal.ofReal (exp (-2*Λ*τ)*‖NativeHeatObservation.kernel ell M hell (τ,f)-
      NativeHeatObservation.kernel ell M hell (τ,g)‖^2)≤
      ENNReal.ofReal (signedHeatSqConstant κ ρ ell M)*NativeSignedClock.kernel Λ ρ τ*
        ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ (f.1-g.1)):=by
  by_cases hτ:0<τ
  · rw [MixedDampedDifferenceEnergy.native_kernel_trace hell hτ f g]
    have hC:0≤signedHeatSqConstant κ ρ ell M:=signedHeatSqConstant_nonneg hκ hρ hρ1 hM
    have hE:0≤StepInput.negativeEnergy κ Λ ρ (f.1-g.1):=
      negativeEnergy_nonneg κ ρ (zero_le_one.trans hΛ) _
    have hA:0≤Λ^ρ*(τ/timeScale)^(-(1/2:ℝ))+(τ/timeScale)^(-(1/2:ℝ)-ρ)+(Λ^ρ+1):=by
      have hpos:0<τ/timeScale:=div_pos hτ timeScale_pos
      positivity
    have hb:=globalSignedHeatEnergy_bound (div_pos hτ timeScale_pos) hκ (zero_lt_one.trans_le hΛ)
      hρ hρ1 f.1 g.1 ell M hell f.2.1 g.2.1 f.2.2 g.2.2
    apply (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hb (exp_pos _).le)).trans_eq
    rw [NativeSignedClock.kernel,indicator_of_mem (show τ∈Ioi (0:ℝ) from hτ)]
    rw [←ENNReal.ofReal_mul hC,←ENNReal.ofReal_mul
      (mul_nonneg hC (mul_nonneg (exp_pos _).le hA))]
    congr 1
    ring
  · rw [NativeHeatObservation.kernel_zero hell (le_of_not_gt hτ) f,
      NativeHeatObservation.kernel_zero hell (le_of_not_gt hτ) g,
      sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,ENNReal.ofReal_zero]
    exact zero_le

variable {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [SFinite μ]

def input_energy (H:ℝ≥0) (f g:ℝ≥0×Ω→EllipticField ell M):ℝ≥0∞:=
  ∫⁻s,∫⁻ω,ENNReal.ofReal (StepInput.negativeEnergy κ Λ ρ ((f (s,ω)).1-(g (s,ω)).1)) ∂μ ∂timeMeasure H

include hκ hΛ hρ hρ1 hM in
/-- The true full native-clock signed stochastic input has the exact
massive energy gain on the original ordered triangle. Coefficient paths
may be arbitrarily dependent; no stochastic isometry is an assumption. -/
theorem causal_energy (H:ℝ≥0) (f g:ℝ≥0×Ω→EllipticField ell M)
    (hf:Measurable f) (hg:Measurable g):
    (∫⁻t,∫⁻s,∫⁻ω,ENNReal.ofReal (exp (-2*Λ*((t:ℝ)-(s:ℝ)))*
      ‖NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),f (s,ω))-
        NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),g (s,ω))‖^2)
        ∂μ ∂timeMeasure H ∂timeMeasure H)≤
      ENNReal.ofReal (signedHeatSqConstant κ ρ ell M*NativeSignedClock.constant ρ*
        signedDampingConstant ρ*Λ^(ρ-1/2))*input_energy (κ:=κ) (Λ:=Λ) (ρ:=ρ) μ H f g:=by
  let C:=signedHeatSqConstant κ ρ ell M
  let F:ℝ≥0→ℝ≥0∞:=fun s=>∫⁻ω,ENNReal.ofReal
    (StepInput.negativeEnergy κ Λ ρ ((f (s,ω)).1-(g (s,ω)).1)) ∂μ
  have hC:0≤C:=signedHeatSqConstant_nonneg hκ hρ hρ1 hM
  have hm:Measurable (fun p:ℝ≥0×Ω=>ENNReal.ofReal
      (StepInput.negativeEnergy κ Λ ρ ((f p).1-(g p).1))):=
    (continuous_negativeEnergy (zero_lt_one.trans_le hΛ) hρ.le).measurable.comp
      ((measurable_subtype_coe.comp hf).sub (measurable_subtype_coe.comp hg)) |>.ennreal_ofReal
  have hF:Measurable F:=hm.lintegral_prod_right'
  calc
    _≤∫⁻t,∫⁻s,ENNReal.ofReal C*NativeSignedClock.kernel Λ ρ ((t:ℝ)-(s:ℝ))*F s
        ∂timeMeasure H ∂timeMeasure H:=by
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro s
      apply (lintegral_mono (fun ω=>point_bound hκ hΛ hρ hρ1 hell hM _ (f (s,ω)) (g (s,ω)))).trans_eq
      exact lintegral_const_mul _ (hm.comp (measurable_const.prodMk measurable_id))
    _=ENNReal.ofReal C*(∫⁻t,∫⁻s,NativeSignedClock.kernel Λ ρ ((t:ℝ)-(s:ℝ))*F s
        ∂timeMeasure H ∂timeMeasure H):=by
      simp_rw [mul_assoc,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤ENNReal.ofReal C*((∫⁻u:ℝ,NativeSignedClock.kernel Λ ρ u)*(∫⁻s,F s ∂timeMeasure H)):=
      mul_le_mul' le_rfl (NativeSignedClock.convolution _ F (NativeSignedClock.kernel_measurable Λ ρ) hF H)
    _≤ENNReal.ofReal C*(ENNReal.ofReal
        (NativeSignedClock.constant ρ*signedDampingConstant ρ*Λ^(ρ-1/2))*(∫⁻s,F s ∂timeMeasure H)):=
      mul_le_mul' le_rfl (mul_le_mul' (NativeSignedClock.mass hΛ hρ.le hρ1) le_rfl)
    _=_:=by
      rw [←mul_assoc,←ENNReal.ofReal_mul hC]
      congr 1
      congr 1
      dsimp only [C]
      ring

end SHE.NativeSignedDamping
