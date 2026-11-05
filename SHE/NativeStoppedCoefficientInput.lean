module
public import SHE.StoppedIntegralEquality
public import SHE.NativeDampedHaarInput
public import SHE.ContinuousHeatMild
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeStoppedCoefficientInput
open Set MeasureTheory PredictableL2 FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance (ell M:ℝ) : MeasurableSpace (EllipticField ell M):=borel _
local instance (ell M:ℝ) : BorelSpace (EllipticField ell M):=⟨rfl⟩
variable{Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable{Λ ell M:ℝ}(hΛ:0≤Λ)(hell:0<ell)(hM:0≤M)
variable{a:ℝ→ℝ}(ha:Measurable a)(hb:∀z,ell≤a z ∧ a z≤M)
variable(hcoef:Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
variable(U V:ℝ≥0→Ω→RealL2)
variable(hU:StronglyMeasurable[𝓕.predictable] (Function.uncurry U))
variable(hV:StronglyMeasurable[𝓕.predictable] (ContinuousHeatMild.coefficientFunction ha hell hb V))
variable(d:Process (E:=RealL2) 𝓕 μ H)

def plus:ℝ≥0×Ω→EllipticField ell M:=fun p=>
  NonlinearHaarIntegrand.coefficientField a ha ell M hell hb (U p.1 p.2+d p)
include hU hcoef in
theorem plus_predictable:StronglyMeasurable[𝓕.predictable] (plus (𝓕:=𝓕) (μ:=μ) (H:=H) (ha:=ha) (hell:=hell) (hb:=hb) (U:=U) (d:=d)):=
  (hcoef.comp (hU.add (Lp.stronglyMeasurable d)).measurable).stronglyMeasurable

include hU hV hcoef in
/-- The stopped-source substitution is an equality of the actual native
Hilbert noise inputs after applying the SAME original integral. -/
theorem integral_equal
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
    (hlocal:StandardTerminalPastLocality I)
    (A:ℝ≥0→Ω→ℝ)(hAa:StronglyAdapted 𝓕 A)(hAc:∀ω,Continuous (fun s=>A s ω))
    (hAm:∀ω,Monotone (fun s=>A s ω))(hH:0<H)
    (hd:∀ᵐp∂energyMeasure μ H,d p=if A p.1 p.2<1 then V p.1 p.2-U p.1 p.2 else 0)
    (q:ℝ≥0)(hq:q≤H)(hq1:(q:ℝ)≤1):
    ∀ᵐω∂μ,A q ω<1→
      I.integral (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM
        (ContinuousHeatMild.coefficientFunction ha hell hb V) hV q hq hq1) ω=
      I.integral (NativeDampedHaarInput.input 𝓕 μ H hΛ hell hM
        (plus (𝓕:=𝓕) (μ:=μ) (H:=H) (ha:=ha) (hell:=hell) (hb:=hb) (U:=U) (d:=d)) (plus_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (ha:=ha) (hell:=hell) (hb:=hb) (hcoef:=hcoef) (U:=U) (hU:=hU) (d:=d)) q hq hq1) ω:=by
  apply StoppedIntegralEquality.equal 𝓕 μ H I hlocal A hAa hAc hAm 1 hH q hq
  filter_upwards [hd,
    NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hell hM
      (ContinuousHeatMild.coefficientFunction ha hell hb V) hV q hq hq1,
    NativeDampedHaarInput.input_ae 𝓕 μ H hΛ hell hM
      (plus (𝓕:=𝓕) (μ:=μ) (H:=H) (ha:=ha) (hell:=hell) (hb:=hb) (U:=U) (d:=d)) (plus_predictable (𝓕:=𝓕) (μ:=μ) (H:=H) (ha:=ha) (hell:=hell) (hb:=hb) (hcoef:=hcoef) (U:=U) (hU:=hU) (d:=d)) q hq hq1]
    with p hd hv hg h
  rw [hv,hg]
  rcases h with hafter|hbefore
  · have hs:(q:ℝ)-(p.1:ℝ)≤0:=sub_nonpos.mpr (by exact_mod_cast hafter.le)
    simp only [NativeDampedHaarInput.raw,NativeFixedHaarInput.raw,
      NativeHeatObservation.kernel_zero hell hs,smul_zero]
  · have he:U p.1 p.2+d p=V p.1 p.2:=by rw [hd,if_pos hbefore];abel
    simp only [NativeDampedHaarInput.raw,NativeFixedHaarInput.raw,plus,
      ContinuousHeatMild.coefficientFunction,he]
end SHE.NativeStoppedCoefficientInput
