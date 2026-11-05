module
public import SHE.HaarConvolutionCongruence
public import SHE.HaarPredictableVersion
public import SHE.NonlinearConvolution
public import SHE.LeftFrozenFiniteHaarOriginalLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ContinuousNonlinearClass
open MeasureTheory PredictableL2 LowBands
open scoped NNReal ENNReal
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hH:(H:ℝ)≤1)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hUa:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun s=>U s ω))
variable(I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(B:ℝ≥0)(hBDG:StandardTerminalBDG16 I B)(hpos:0<H)
include hBDG hpos in
/-- A continuous convolution built from an actual version is exactly
its nonlinear predictable-L2 class. No pathwise limit is assumed. -/
theorem version_ae(u:Process (E:=StateL2) 𝓕 μ H)
    (hu:(fun p:ℝ≥0×Ω=>U p.1 p.2)=ᵐ[energyMeasure μ H] u):
    (fun p:ℝ≥0×Ω=>HaarContinuousVersion.version 𝓕 μ H hH hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2))
      (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U)
      (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) I p.1 p.2)=ᵐ[energyMeasure μ H]
      NonlinearConvolution.map 𝓕 μ H ha hell hb hβ hHolder hholder I u:=by
  have he:LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U=ᵐ[energyMeasure μ H]
      NonlinearConvolution.field 𝓕 μ H ha hell hb u:=by
    filter_upwards [hu] with p hp
    exact congrArg (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb) hp
  have hec:=HaarStochasticConvolution.convolution_congr_ae 𝓕 μ H hH hell
    (hell.le.trans ((hb 0).1.trans (hb 0).2)) I
    (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U)
    (NonlinearConvolution.field 𝓕 μ H ha hell hb u)
    (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc)
    (NonlinearConvolution.field_predictable 𝓕 μ H ha hell hb hβ hHolder hholder u) he
  have hv:=HaarPredictableVersion.convolution_ae_version 𝓕 μ H hH hell
    (hell.le.trans ((hb 0).1.trans (hb 0).2))
    (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U)
    (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) I B hBDG hpos
  rw [hec] at hv
  exact hv.symm
end SHE.ContinuousNonlinearClass
