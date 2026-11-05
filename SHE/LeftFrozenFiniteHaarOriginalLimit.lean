module
public import SHE.LeftFrozenFiniteHaarInput
public import SHE.HaarFixedApproximation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.LeftFrozenFiniteHaarOriginalLimit
open MeasureTheory Set Filter PredictableL2 LowBands NonlinearHaarIntegrand
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hH:(H:ℝ)≤1)
variable {a:ℝ→ℝ}(ha:Measurable a){ell M Holder β:ℝ}(hell:0<ell)
variable(hb:∀z,ell≤a z∧a z≤M)(hβ:0<β)(hHolder:0≤Holder)
variable(hholder:∀z w,|a z-a w|≤Holder*|z-w|^β)
variable(U:ℝ≥0→Ω→StateL2)(hUa:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun s=>U s ω))
variable {L:ℝ≥0}(hLip:LipschitzWith L (fun z=>(a z:ℂ)))

def field:ℝ≥0×Ω→FiniteHaar.EllipticField ell M:=
  fun p=>coefficientField a ha ell M hell hb (U p.1 p.2)

include hβ hHolder hholder hUa hc in
theorem field_predictable:StronglyMeasurable[𝓕.predictable] (field ha hell hb U):=
  ((coefficientField_measurable ha hell hb hβ hHolder hholder).comp
    (ContinuousPredictable.stronglyMeasurable 𝓕 U hUa hc).measurable).stronglyMeasurable

include hLip in
/-- Finite original predictable time-cell integrals with actual past
coefficient values converge strongly to the original nonlinear stochastic
convolution. This proves the stochastic consistency needed for law
transfer rather than taking it as an approximation hypothesis. -/
theorem integral_tendsto
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
    (t:ℝ≥0)(ht:t≤H):
    Tendsto (fun n=>I.integral
      (LeftFrozenFiniteHaarInput.input 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t)) atTop
      (𝓝 (TerminalHaarConvolution.value 𝓕 μ H hH hell
        (hell.le.trans ((hb 0).1.trans (hb 0).2)) (field ha hell hb U)
        (field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) I t ht)):=by
  have hmU:Measurable (Function.uncurry U):=
    ((ContinuousPredictable.stronglyMeasurable 𝓕 U hUa hc).mono (predictable_le_product 𝓕)).measurable
  let E:ℕ→ℝ≥0∞:=fun n=>∫⁻p:ℝ≥0×Ω,ENNReal.ofReal
    (‖LeftFrozenFiniteHaarKernel.value ha hell hb U n (t,p)-
      kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2) ∂energyMeasure μ H
  have he:Tendsto E atTop (𝓝 0):=
    LeftFrozenFiniteHaarConsistency.input_energy_tendsto μ H hH ha hell hb hβ hHolder hholder U hmU hc hLip t ht
  apply KernelEnergyCauchy.tendsto_of_energy_error _ _ E he
  intro n
  rw [TerminalHaarConvolution.value,I.difference_energy]
  apply le_of_eq
  have hm:Measurable (fun p:ℝ≥0×Ω=>ENNReal.ofReal
      (‖LeftFrozenFiniteHaarKernel.value ha hell hb U n (t,p)-
        kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2)):=by
    exact ENNReal.continuous_ofReal.measurable.comp
      ((((LeftFrozenFiniteHaarKernel.value_measurable ha hell hb U hβ hHolder hholder hmU n).comp
        (measurable_const.prodMk measurable_id)).sub
        ((kernel_measurable ha hell hb hβ hHolder hholder).comp
          ((measurable_const.sub (measurable_coe_nnreal_real.comp measurable_fst)).prodMk hmU))).norm.pow_const 2)
  change _=∫⁻p:ℝ≥0×Ω,ENNReal.ofReal
      (‖LeftFrozenFiniteHaarKernel.value ha hell hb U n (t,p)-
        kernel a ha ell M hell hb ((t:ℝ)-(p.1:ℝ),U p.1 p.2)‖^2) ∂(timeMeasure H).prod μ
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod
      (LeftFrozenFiniteHaarInput.input_ae 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t),
    Measure.ae_ae_of_ae_prod (FixedHaarIntegral.input_ae 𝓕 μ H hH hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2)) (field ha hell hb U)
      (field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) t ht)] with s hs hs'
  apply lintegral_congr_ae
  filter_upwards [hs,hs'] with ω hω hω'
  rw [hω,hω']
  rfl
end SHE.LeftFrozenFiniteHaarOriginalLimit
