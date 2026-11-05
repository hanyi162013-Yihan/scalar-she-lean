module
public import SHE.ContinuousPicardIterationData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000

namespace SHE.ContinuousPicardIterates
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

variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(J:Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)

variable (B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable (hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)


variable (z:ℝ≥0→StateL2)


variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
variable {Ω':Type*}[MeasurableSpace Ω']
include hLip hIJ hlocal hBDG hpos in
/-- Every actual continuous Picard iterate has the same full joint law
with the two drivers on unrelated original probability spaces. -/
theorem law_of_recursion(hz:Continuous z)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hnull':NullCompleteFiltration.ContainsNullSets 𝓖 ν)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (hDriver:μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H J b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H J' b i t ω)):
    ∀(X:ℕ→Bool→ℝ≥0→Ω→StateL2)(hXa:∀n b,StronglyAdapted 𝓕 (X n b))
      (hXc:∀n b ω,Continuous (fun t=>X n b t ω))
      (Y:ℕ→Bool→ℝ≥0→Ω'→StateL2)(hYa:∀n b,StronglyAdapted 𝓖 (Y n b))
      (hYc:∀n b ω,Continuous (fun t=>Y n b t ω)),
      X 0=(fun _ _ _=>0)→Y 0=(fun _ _ _=>0)→
      (∀n,X (n+1)=ContinuousPicardStepLaw.step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder
        (X n) (hXa n) (hXc n) I z)→
      (∀n,Y (n+1)=ContinuousPicardStepLaw.step 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder
        (Y n) (hYa n) (hYc n) I' z)→
      ∀n:ℕ,μ.map (TwoChannelConvolutionLaw.source 𝓕 μ H (X n) J)=
        ν.map (TwoChannelConvolutionLaw.source 𝓖 ν H (Y n) J'):=by
  intro X hXa hXc Y hYa hYc hX0 hY0 hXs hYs n
  induction n with
  |zero=>
    let e:(Bool→FiniteHaar.HaarNode→ℝ≥0→ℝ)→Source:=fun w=>(fun _ _=>0,w)
    have hm:Measurable e:=measurable_const.prodMk measurable_id
    have hd:=congrArg (fun P:Measure (Bool→FiniteHaar.HaarNode→ℝ≥0→ℝ)=>P.map e) hDriver
    have hJ:Measurable (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H J b i t ω):=
      measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr (fun i=>measurable_pi_iff.mpr
        (fun t=>LeftFrozenConvolutionLaw.driver_measurable 𝓕 μ H (J b) i t)))
    have hJ':Measurable (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H J' b i t ω):=
      measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr (fun i=>measurable_pi_iff.mpr
        (fun t=>LeftFrozenConvolutionLaw.driver_measurable 𝓖 ν H (J' b) i t)))
    rw [Measure.map_map hm hJ,Measure.map_map hm hJ'] at hd
    rw [hX0,hY0]
    exact hd
  |succ n ih=>
    rw [hXs,hYs]
    exact ContinuousPicardStepLaw.law 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder
      (X n) (hXa n) (hXc n)
      L hLip I J B hBDG hpos z hIJ hlocal 𝓖 ν
      (Y n) (hYa n) (hYc n)
      I' J' hBDG' hIJ' hlocal' ih
end SHE.ContinuousPicardIterates
