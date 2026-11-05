module
public import SHE.LeftFrozenFiniteHaarOriginalLimit
public import SHE.LeftFrozenFiniteHaarFunctional
public import SHE.CommonLawLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.LeftFrozenConvolutionLaw
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


def driver(J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H):
    FiniteHaar.HaarNode→ℝ≥0→Ω→ℝ:=fun i=>BoundedHilbertItoCell.driver 𝓕 μ H i J

theorem driver_measurable(J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (i:FiniteHaar.HaarNode)(s:ℝ≥0):Measurable (driver 𝓕 μ H J i s):=
  (Lp.stronglyMeasurable (J.integral _)).measurable

include hH hβ hHolder hholder hUa hc hLip in
theorem in_measure
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)
    (hlocal:StandardTerminalPastLocality J)(t:ℝ≥0)(ht:t≤H):
    TendstoInMeasure μ
      (fun n=>LeftFrozenFiniteHaarIntegral.value ha hell hb U n t (driver 𝓕 μ H J)) atTop
      (TerminalHaarConvolution.value 𝓕 μ H hH hell
        (hell.le.trans ((hb 0).1.trans (hb 0).2)) (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U)
        (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) I t ht):=by
  exact (tendstoInMeasure_of_tendsto_Lp
    (LeftFrozenFiniteHaarOriginalLimit.integral_tendsto 𝓕 μ H hH ha hell hb hβ hHolder hholder U hUa hc hLip I t ht)).congr
      (fun n=>LeftFrozenFiniteHaarIntegral.integral_ae 𝓕 μ H ha hell hb hβ hHolder hholder U hUa n t I J hIJ hlocal)
      Filter.EventuallyEq.rfl

variable {Ω':Type*}[MeasurableSpace Ω']
include hH hβ hHolder hholder hUa hc hLip in
/-- Original smooth stochastic convolutions on different spaces have
one marginal law whenever the true input/driver joint laws agree. All
finite stochastic approximation and limit applicability is derived. -/
theorem law(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (V:ℝ≥0→Ω'→StateL2)(hVa:StronglyAdapted 𝓖 V)(hVc:∀ω,Continuous (fun s=>V s ω))
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (I':StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hIJ:NativeObservationNaturality.StandardScalarNaturality I J)
    (hIJ':NativeObservationNaturality.StandardScalarNaturality I' J')
    (hlocal:StandardTerminalPastLocality J)(hlocal':StandardTerminalPastLocality J')
    (hLaw:μ.map (fun ω=>((fun s=>U s ω),fun i s=>driver 𝓕 μ H J i s ω))=
      ν.map (fun ω=>((fun s=>V s ω),fun i s=>driver 𝓖 ν H J' i s ω)))
    (t:ℝ≥0)(ht:t≤H):
    μ.map (TerminalHaarConvolution.value 𝓕 μ H hH hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2)) (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb U)
      (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 ha hell hb hβ hHolder hholder U hUa hc) I t ht)=
    ν.map (TerminalHaarConvolution.value 𝓖 ν H hH hell
      (hell.le.trans ((hb 0).1.trans (hb 0).2)) (LeftFrozenFiniteHaarOriginalLimit.field ha hell hb V)
      (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓖 ha hell hb hβ hHolder hholder V hVa hVc) I' t ht):=by
  have hmU:Measurable (Function.uncurry U):=
    ((ContinuousPredictable.stronglyMeasurable 𝓕 U hUa hc).mono (predictable_le_product 𝓕)).measurable
  have hmV:Measurable (Function.uncurry V):=
    ((ContinuousPredictable.stronglyMeasurable 𝓖 V hVa hVc).mono (predictable_le_product 𝓖)).measurable
  have hu:∀s,Measurable (U s):=fun s=>hmU.comp (measurable_const.prodMk measurable_id)
  have hv:∀s,Measurable (V s):=fun s=>hmV.comp (measurable_const.prodMk measurable_id)
  let f:ℕ→Ω→StateL2:=fun n=>LeftFrozenFiniteHaarIntegral.value ha hell hb U n t (driver 𝓕 μ H J)
  let g:ℕ→Ω'→StateL2:=fun n=>LeftFrozenFiniteHaarIntegral.value ha hell hb V n t (driver 𝓖 ν H J')
  have hf(n:ℕ):Measurable (f n):=by
    have hh:Measurable (fun ω=>((fun s=>U s ω),fun i s=>driver 𝓕 μ H J i s ω)):=
      (measurable_pi_iff.mpr hu).prodMk (measurable_pi_iff.mpr
        (fun i=>measurable_pi_iff.mpr (fun s=>driver_measurable 𝓕 μ H J i s)))
    simpa only [f,Function.comp_def,LeftFrozenFiniteHaarFunctional.functional_eval] using
      (LeftFrozenFiniteHaarFunctional.functional_measurable ha hell hb hβ hHolder hholder n t).comp hh
  have hg(n:ℕ):Measurable (g n):=by
    have hh:Measurable (fun ω=>((fun s=>V s ω),fun i s=>driver 𝓖 ν H J' i s ω)):=
      (measurable_pi_iff.mpr hv).prodMk (measurable_pi_iff.mpr
        (fun i=>measurable_pi_iff.mpr (fun s=>driver_measurable 𝓖 ν H J' i s)))
    simpa only [g,Function.comp_def,LeftFrozenFiniteHaarFunctional.functional_eval] using
      (LeftFrozenFiniteHaarFunctional.functional_measurable ha hell hb hβ hHolder hholder n t).comp hh
  apply CommonLawLimit.map_eq μ ν f g _ _ (fun n=>(hf n).aemeasurable) (fun n=>(hg n).aemeasurable)
    (in_measure 𝓕 μ H hH ha hell hb hβ hHolder hholder U hUa hc hLip I J hIJ hlocal t ht)
    (in_measure 𝓖 ν H hH ha hell hb hβ hHolder hholder V hVa hVc hLip I' J' hIJ' hlocal' t ht)
  intro n
  exact LeftFrozenFiniteHaarFunctional.law μ ha hell hb hβ hHolder hholder U ν V
    (driver 𝓕 μ H J) (driver 𝓖 ν H J') hu hv (driver_measurable 𝓕 μ H J)
    (driver_measurable 𝓖 ν H J') hLaw n t
end SHE.LeftFrozenConvolutionLaw
