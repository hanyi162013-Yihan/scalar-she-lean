module

public import SHE.NativeRandomKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NativeKernelNashEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
open scoped ENNReal
local instance nativeKernelNashEnergy_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeKernelNashEnergy_unitPeriod:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeKernelNashEnergy_unitSigma:MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeKernelNashEnergy_unitBorel:BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeKernelNashEnergy_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance nativeKernelNashEnergy_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]

def unitColumns (F:Ω×(HeatCircle×HeatCircle)→ℂ):
    (Ω×HeatCircle)×UnitAddCircle→ℂ:=
  NativeRandomRows.unitField (NativeRandomKernel.columnField F)

def unitRow (F:Ω×(HeatCircle×HeatCircle)→ℂ) (p:Ω×HeatCircle):CircleHeat.CircleL2:=
  RandomRowEnergy.row (unitColumns F) p

def columnOne (F:Ω×(HeatCircle×HeatCircle)→ℂ) (p:Ω×HeatCircle):ℝ:=
  HeatMarkov.normOne (unitRow F p)

/-- Native negative-output energy follows from the ACTUAL integrated
column L1-square and L2-square masses. These may arise from a variable
output L2 amplitude; no pointwise spatial supremum is used. All native
column realization, Borel and Fubini applicability are derived here. -/
theorem from_column_masses (μ:Measure Ω) [IsProbabilityMeasure μ]
    {F:Ω×(HeatCircle×HeatCircle)→ℂ} (hF:Measurable F)
    {B:ℝ} (hB:0≤B) (hb:∀ω y x,‖F (ω,(y,x))‖≤B)
    {Λ ρ t M1 M2:ℝ} (hΛ:1≤Λ) (hρ:0<ρ) (hρhalf:ρ<1/2)
    (ht:0<t) (ht1:t≤1)
    (h1i:Integrable (fun p:Ω×HeatCircle=>columnOne F p^2) (μ.prod haarAddCircle))
    (h1:(∫p:Ω×HeatCircle,columnOne F p^2 ∂μ.prod haarAddCircle)≤M1)
    (h2:(∫p:Ω×HeatCircle,‖NativeRandomKernel.column F p‖^2 ∂μ.prod haarAddCircle)≤M2):
    Integrable (fun ω=>‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2) μ ∧
      (∫ω,‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2 ∂μ)≤
        ((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeHeatSpan.clock t)^(ρ-1/2))*M1+
          (NativeHeatSpan.clock t)^ρ*M2:=by
  let V:=NativeRandomKernel.column F
  let Q:=NativeRandomKernel.negativeColumn Λ ρ hΛ hρ.le F
  have hVm:Measurable V:=NativeRandomKernel.column_measurable hF hb
  have hQm:Measurable Q:=NativeRandomKernel.negativeColumn_measurable hΛ hρ.le hF hb
  have hVi:Integrable (fun p:Ω×HeatCircle=>‖V p‖^2) (μ.prod haarAddCircle):=
    (integrable_const (B^2)).mono' (hVm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun p=>by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (NativeRandomKernel.column_norm_le hF hB hb p) 2))
  have hQi:Integrable (fun p:Ω×HeatCircle=>‖Q p‖^2) (μ.prod haarAddCircle):=
    (integrable_const (B^2)).mono' (hQm.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun p=>by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (NativeRandomKernel.negativeColumn_norm_le hΛ hρ.le hF hB hb p) 2))
  let c1:=(1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeHeatSpan.clock t)^(ρ-1/2)
  let c2:=(NativeHeatSpan.clock t)^ρ
  have hc1:0≤c1:=by
    dsimp [c1]
    have hg:0≤HeatTrace.fractionalGaussianIntegral ρ:=
      (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (NativeHeatSpan.clock_pos ht).le _)
  have hc2:0≤c2:=rpow_nonneg (NativeHeatSpan.clock_pos ht).le _
  have hp(p:Ω×HeatCircle):‖Q p‖^2≤c1*columnOne F p^2+c2*‖V p‖^2:=by
    have hclock:0<NativeHeatSpan.clock t:=NativeHeatSpan.clock_pos ht
    have hden:1≤4*π^2:=by nlinarith [Real.two_le_pi]
    have hc:(NativeHeatSpan.clock t)≤1:=
      (div_le_one (by positivity:0<4*π^2)).mpr (ht1.trans hden)
    have he:V p=CircleNormalization.push (unitRow F p):=rfl
    have hq:‖Q p‖^2=NegativeNash.energy Λ ρ (unitRow F p):=by
      change ‖OneInputOperator.besselHalf Λ ρ hΛ hρ.le (V p)‖^2=_
      rw [he,CircleNormalization.push_bessel_energy hΛ hρ.le,
        NegativeNash.energy_eq_negativeEnergy Λ ρ (zero_lt_one.trans_le hΛ)]
    have hh:=NegativeNash.energy_cutoff hΛ hρ hρhalf hclock hc (unitRow F p)
    rw [hq,he,CircleNormalization.push.norm_map]
    exact hh
  have hmass:(∫p:Ω×HeatCircle,‖Q p‖^2 ∂μ.prod haarAddCircle)≤c1*M1+c2*M2:=by
    have hh:=(integral_mono hQi ((h1i.const_mul c1).add (hVi.const_mul c2)) hp)
    change (∫p:Ω×HeatCircle,‖Q p‖^2 ∂μ.prod haarAddCircle)≤
      ∫p:Ω×HeatCircle,c1*columnOne F p^2+c2*‖V p‖^2 ∂μ.prod haarAddCircle at hh
    rw [integral_add (h1i.const_mul c1) (hVi.const_mul c2),integral_const_mul,integral_const_mul] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left h1 hc1) (mul_le_mul_of_nonneg_left h2 hc2))
  have he(ω:Ω):‖NativeRandomKernel.negativeKernel Λ ρ hΛ hρ.le F ω‖^2=
      ∫y:HeatCircle,‖Q (ω,y)‖^2 ∂haarAddCircle:=
    HilbertL2Fields.realize_norm_sq Q (NativeRandomKernel.negativeColumn_memLp hΛ hρ.le hF hB hb) ω
  refine ⟨?_,?_⟩
  · simp_rw [he]
    exact hQi.integral_prod_left
  · simp_rw [he]
    rw [←integral_prod _ hQi]
    exact hmass

end SHE.NativeKernelNashEnergy
