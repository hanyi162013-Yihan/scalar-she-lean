module

public import SHE.NativeKernelOutputEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.NativeHeatOutputEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance nativeHeatOutputEnergy_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeHeatOutputEnergy_unitPeriod:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeHeatOutputEnergy_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeHeatOutputEnergy_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
local instance nativeHeatOutputEnergy_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeHeatOutputEnergy_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

/-- The sharp native heat/Bessel trace retains a genuinely spatial L2
output amplitude. The amplitude need not have any spatial supremum. -/
theorem energy (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    (a:HeatCircle→ℝ) (ha:Measurable a) (ha0:∀x,0≤a x)
    (hai:Integrable (fun x=>a x^2) haarAddCircle) {E:ℝ}
    (he:(∫x,a x^2 ∂haarAddCircle)≤E)
    {Λ ρ t:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2) (ht:0<t) (ht1:t≤1)
    (hsharp:∀y x,ProfileL2.normTwo μ (fun ω=>‖F (ω,(y,x))‖)≤
      a x*‖NativeHeatSpan.kernel (8*t) (by positivity) y x‖):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        GaussianNegativePacket.constant ρ*(NativeHeatSpan.clock t)^(ρ-1/2)*E:=by
  let k:HeatCircle×HeatCircle→ℝ:=fun z=>‖NativeHeatSpan.kernel (8*t) (by positivity) z.1 z.2‖
  have hkm:Measurable k:=by
    simp_rw [k,NativeHeatSpan.kernel_eq_physical]
    exact (NativeHeatSpan.continuous_heatPhysical_space (by positivity:0<8*t)).norm.measurable
  have hk0(z):0≤k z:=norm_nonneg _
  have hrow(y:HeatCircle):Integrable (fun x=>k (y,x)) haarAddCircle ∧
      (∫x,k (y,x) ∂haarAddCircle)=1:=
    ⟨(NativeHeatSpan.kernel (8*t) (by positivity) y).continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _),NativeHeatSpan.kernel_norm_mass (by positivity) y⟩
  have hcol(x:HeatCircle):Integrable (fun y=>k (y,x)) haarAddCircle ∧
      (∫y,k (y,x) ∂haarAddCircle)≤1:=by
    have he:(fun y:HeatCircle=>k (y,x))=(fun y=>k (x,y)):=by
      funext y
      exact congrArg norm (NativeHeatSpan.kernel_symm (by positivity:0<8*t) y x)
    rw [he]
    exact ⟨(hrow x).1,(hrow x).2.le⟩
  have hclock:0<NativeHeatSpan.clock t:=NativeHeatSpan.clock_pos ht
  have hclock1:NativeHeatSpan.clock t≤1:=by
    have hd:1≤4*π^2:=by nlinarith [Real.two_le_pi]
    exact (div_le_one (by positivity:0<4*π^2)).mpr (ht1.trans hd)
  let J:=GaussianNegativePacket.traceConstant*(NativeHeatSpan.clock t)^(-(1/2:ℝ))
  have hJ:0≤J:=mul_nonneg GaussianNegativePacket.traceConstant_pos.le (rpow_nonneg hclock.le _)
  have hs(x:HeatCircle):Integrable (fun y=>k (y,x)^2) haarAddCircle ∧
      (∫y,k (y,x)^2 ∂haarAddCircle)≤J:=by
    have hc:Continuous (fun y:HeatCircle=>k (y,x)^2):=by
      simp_rw [k,NativeHeatSpan.kernel_symm (by positivity:0<8*t)]
      exact (NativeHeatSpan.kernel (8*t) (by positivity) x).continuous.norm.pow 2
    refine ⟨hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _),?_⟩
    have he:(∫y,k (y,x)^2 ∂haarAddCircle)=‖circleHeat (8*t) x‖^2:=by
      rw [StoppedFourier.L2_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [ProfileVariance.heatPhysical_ae (by positivity:0<8*t) x] with y hy
      change ‖NativeHeatSpan.kernel (8*t) (by positivity) y x‖^2=‖circleHeat (8*t) x y‖^2
      rw [NativeHeatSpan.kernel_symm (by positivity:0<8*t) y x,NativeHeatSpan.kernel_eq_physical,hy]
    rw [he,←NativeHeatSpan.push_unit_kernel,CircleNormalization.push.norm_map]
    have heclock:NativeHeatSpan.clock (8*t)=8*NativeHeatSpan.clock t:=by unfold NativeHeatSpan.clock; ring
    rw [heclock]
    exact GaussianNegativePacket.kernel_eight_norm_sq hclock hclock1 _
  have hh:=NativeKernelOutputEnergy.from_rms_envelope μ hF hB hb a ha ha0 hai he hJ
    k hkm hk0 hrow hcol hs hsharp hΛ hρ hρhalf ht ht1
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  dsimp only [J]
  rw [show (NativeHeatSpan.clock t)^ρ*(GaussianNegativePacket.traceConstant*
      (NativeHeatSpan.clock t)^(-(1/2:ℝ))*E)=
      GaussianNegativePacket.traceConstant*((NativeHeatSpan.clock t)^ρ*
        (NativeHeatSpan.clock t)^(-(1/2:ℝ)))*E by ring,
    ←Real.rpow_add hclock]
  unfold GaussianNegativePacket.constant
  rw [show ρ+(-(1/2:ℝ))=ρ-1/2 by ring]
  ring

end SHE.NativeHeatOutputEnergy
