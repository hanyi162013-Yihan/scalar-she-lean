module
public import SHE.TwoChannelContinuousLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.ContinuousPicardStepLaw
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


variable (z:ℝ≥0→StateL2)

def step(b:Bool)(t:ℝ≥0)(ω:Ω):StateL2:=if b then 0 else
  z t+TwoChannelContinuousLaw.convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I true t ω+
    TwoChannelContinuousLaw.convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I false t ω

def decode(w:Tag→JointState):Source:=
  ((fun b t=>if b then 0 else z t+(w (.inl (true,t))).1+(w (.inl (false,t))).1),
    fun b i t=>(w (.inr (b,i,t))).2)

theorem decode_measurable:Measurable (decode z):=by
  apply Measurable.prodMk
  · apply measurable_pi_iff.mpr
    intro b
    apply measurable_pi_iff.mpr
    intro t
    cases b with
    | false=>exact ((measurable_const.add (measurable_fst.comp (measurable_pi_apply (Sum.inl (true,t):Tag)))).add
        (measurable_fst.comp (measurable_pi_apply (Sum.inl (false,t):Tag))))
    | true=>exact measurable_const
  · apply measurable_pi_iff.mpr
    intro b
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro t
    exact measurable_snd.comp (measurable_pi_apply (Sum.inr (b,i,t):Tag))

include hBDG hpos hnull in
theorem step_adapted:∀b,StronglyAdapted 𝓕
    (step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I z b):=by
  intro b t
  cases b with
  | true=>exact stronglyMeasurable_const
  | false=>exact ((stronglyMeasurable_const.add
      (TwoChannelContinuousLaw.convolution_adapted 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I B hBDG hpos hnull true t)).add
      (TwoChannelContinuousLaw.convolution_adapted 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I B hBDG hpos hnull false t))

include hpos in
theorem step_continuous(hz:Continuous z):∀b ω,Continuous
    (fun t=>step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I z b t ω):=by
  intro b ω
  cases b with
  | true=>exact continuous_const
  | false=>exact ((hz.add
      (TwoChannelContinuousLaw.convolution_continuous 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I hpos true ω)).add
      (TwoChannelContinuousLaw.convolution_continuous 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I hpos false ω))

variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
variable {Ω':Type*}[MeasurableSpace Ω']
include hLip hIJ hlocal hBDG hpos in
/-- One literal continuous stochastic Picard step preserves the full
joint law with BOTH original noise channels. -/
theorem law(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (V:Bool→ℝ≥0→Ω'→StateL2)(hVa:∀b,StronglyAdapted 𝓖 (V b))(hVc:∀b ω,Continuous (fun t=>V b t ω))
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (hLaw:μ.map (TwoChannelConvolutionLaw.source 𝓕 μ H U J)=ν.map (TwoChannelConvolutionLaw.source 𝓖 ν H V J')):
    μ.map (TwoChannelConvolutionLaw.source 𝓕 μ H
      (step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I z) J)=
    ν.map (TwoChannelConvolutionLaw.source 𝓖 ν H
      (step 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' z) J'):=by
  have hh:=TwoChannelContinuousLaw.joint_law 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc L hLip I J B hBDG hpos hIJ hlocal
    𝓖 ν V hVa hVc I' J' hBDG' hIJ' hlocal' hLaw
  have hd:=congrArg (fun P:Measure (Tag→JointState)=>P.map (decode z)) hh
  rw [Measure.map_map (decode_measurable z)
      (measurable_pi_iff.mpr (TwoChannelContinuousLaw.process_measurable 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J B hBDG hpos)),
    Measure.map_map (decode_measurable z)
      (measurable_pi_iff.mpr (TwoChannelContinuousLaw.process_measurable 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J' B hBDG' hpos))] at hd
  exact hd
end SHE.ContinuousPicardStepLaw
