module
public import SHE.TwoChannelConvolutionLaw
public import SHE.HaarPredictableVersion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.TwoChannelContinuousLaw
open MeasureTheory Set Filter PredictableL2 LowBands
open scoped NNReal ENNReal Topology
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤):=⟨by simp⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)(hH:(H:ℝ)≤1)
variable(a:Bool→ℝ→ℝ)(ha:∀b,Measurable (a b))(ell M Holder:Bool→ℝ)
variable(hell:∀b,0<ell b)(hb:∀b z,ell b≤a b z∧a b z≤M b)
variable(β:ℝ)(hβ:0<β)(hHolder:∀b,0≤Holder b)
variable(hholder:∀b z w,|a b z-a b w|≤Holder b*|z-w|^β)
variable(U:Bool→ℝ≥0→Ω→StateL2)(hUa:∀b,StronglyAdapted 𝓕 (U b))
variable(hc:∀b ω,Continuous (fun t=>U b t ω))
variable(L:Bool→ℝ≥0)(hLip:∀b,LipschitzWith (L b) (fun z=>(a b z:ℂ)))
abbrev Source:=(Bool→ℝ≥0→StateL2)×(Bool→FiniteHaar.HaarNode→ℝ≥0→ℝ)
abbrev Tag:=Sum (Bool×ℝ≥0) (Bool×FiniteHaar.HaarNode×ℝ≥0)
abbrev JointState:=StateL2×ℝ

variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(J:Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)

variable (B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable (hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)

def convolution(b:Bool):ℝ≥0→Ω→StateL2:=
  HaarContinuousVersion.version 𝓕 μ H hH (hell b)
    ((hell b).le.trans ((hb b 0).1.trans (hb b 0).2))
    (LeftFrozenFiniteHaarOriginalLimit.field (ha b) (hell b) (hb b) (U b))
    (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 (ha b) (hell b) (hb b) hβ (hHolder b)
      (hholder b) (U b) (hUa b) (hc b)) (I b)

include hBDG hpos in
theorem convolution_measurable(b:Bool)(t:ℝ≥0):Measurable
    (convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I b t):=
  HaarContinuousVersion.version_measurable _ _ _ _ _ _ _ _ _ (B b) (hBDG b) hpos t

include hBDG hpos hnull in
theorem convolution_adapted(b:Bool):StronglyAdapted 𝓕
    (convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I b):=
  HaarPredictableVersion.stronglyAdapted_version _ _ _ _ _ _ _ _ _ (B b) (hBDG b) hnull hpos

include hpos in
theorem convolution_continuous(b:Bool)(ω:Ω):Continuous
    (fun t=>convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I b t ω):=
  HaarContinuousVersion.continuous_version _ _ _ _ _ _ _ _ _ hpos ω

def process(i:Tag)(ω:Ω):JointState:=match i with
  | .inl p=>(convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I p.1 p.2 ω,0)
  | .inr p=>(0,TwoChannelConvolutionLaw.driver 𝓕 μ H J p.1 p.2.1 p.2.2 ω)

include hBDG hpos in
theorem process_measurable(i:Tag):Measurable
    (process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i):=by
  cases i with
  | inl p=>exact (convolution_measurable 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I B hBDG hpos p.1 p.2).prodMk measurable_const
  | inr p=>exact measurable_const.prodMk (LeftFrozenConvolutionLaw.driver_measurable 𝓕 μ H (J p.1) p.2.1 p.2.2)

include hBDG hpos in
theorem process_ae(i:Tag):
    process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i =ᵐ[μ]
      TwoChannelConvolutionLaw.process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i:=by
  cases i with
  | inr p=>exact Filter.EventuallyEq.rfl
  | inl p=>
    have he:=HaarContinuousVersion.version_ae 𝓕 μ H hH (hell p.1)
      ((hell p.1).le.trans ((hb p.1 0).1.trans (hb p.1 0).2))
      (LeftFrozenFiniteHaarOriginalLimit.field (ha p.1) (hell p.1) (hb p.1) (U p.1))
      (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 (ha p.1) (hell p.1) (hb p.1) hβ (hHolder p.1)
        (hholder p.1) (U p.1) (hUa p.1) (hc p.1)) (I p.1) (B p.1) (hBDG p.1) hpos p.2
    filter_upwards [he] with ω hω
    exact Prod.ext hω rfl

variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
variable {Ω':Type*}[MeasurableSpace Ω']
include hLip hIJ hlocal hBDG hpos in
/-- Genuine continuous versions retain the full dependent law of both
convolutions and both original drivers. Fixed-time modification suffices. -/
theorem joint_law(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (V:Bool→ℝ≥0→Ω'→StateL2)(hVa:∀b,StronglyAdapted 𝓖 (V b))(hVc:∀b ω,Continuous (fun t=>V b t ω))
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (hLaw:μ.map (TwoChannelConvolutionLaw.source 𝓕 μ H U J)=ν.map (TwoChannelConvolutionLaw.source 𝓖 ν H V J')):
    μ.map (fun ω=>fun i:Tag=>process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i ω)=
      ν.map (fun ω=>fun i:Tag=>process 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J' i ω):=by
  apply CylindricalFunctionalLawLimit.law μ ν (TwoChannelConvolutionLaw.source 𝓕 μ H U J)
    (TwoChannelConvolutionLaw.source 𝓖 ν H V J')
    (TwoChannelConvolutionLaw.source_measurable 𝓕 μ H U hUa J)
    (TwoChannelConvolutionLaw.source_measurable 𝓖 ν H V hVa J') hLaw
    (TwoChannelConvolutionLaw.encoded H a ha ell M hell hb)
    (TwoChannelConvolutionLaw.encoded_measurable H a ha ell M Holder hell hb β hβ hHolder hholder)
    _ _ (process_measurable 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J B hBDG hpos)
    (process_measurable 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J' B hBDG' hpos)
  · intro i
    exact (TwoChannelConvolutionLaw.encoded_in_measure 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc L hLip I J hIJ hlocal i).congr_right
      (process_ae 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J B hBDG hpos i).symm
  · intro i
    exact (TwoChannelConvolutionLaw.encoded_in_measure 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc L hLip I' J' hIJ' hlocal' i).congr_right
      (process_ae 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J' B hBDG' hpos i).symm
end SHE.TwoChannelContinuousLaw
