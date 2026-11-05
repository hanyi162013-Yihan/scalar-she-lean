module
public import SHE.LeftFrozenConvolutionLaw
public import SHE.CylindricalFunctionalLawLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.TwoChannelConvolutionLaw
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

def driver(b:Bool):FiniteHaar.HaarNode→ℝ≥0→Ω→ℝ:=LeftFrozenConvolutionLaw.driver 𝓕 μ H (J b)

def source(ω:Ω):Source:=((fun b t=>U b t ω),fun b i t=>driver 𝓕 μ H J b i t ω)

def convolution(b:Bool)(t:ℝ≥0):Ω→StateL2:=
  TerminalHaarConvolution.value 𝓕 μ H hH (hell b)
    ((hell b).le.trans ((hb b 0).1.trans (hb b 0).2))
    (LeftFrozenFiniteHaarOriginalLimit.field (ha b) (hell b) (hb b) (U b))
    (LeftFrozenFiniteHaarOriginalLimit.field_predictable 𝓕 (ha b) (hell b) (hb b) hβ (hHolder b)
      (hholder b) (U b) (hUa b) (hc b)) (I b) (min t H) (min_le_right _ _)

def process(i:Tag)(ω:Ω):JointState:=match i with
  | .inl p=>(convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I p.1 p.2 ω,0)
  | .inr p=>(0,driver 𝓕 μ H J p.1 p.2.1 p.2.2 ω)

def encoded(n:ℕ)(i:Tag)(z:Source):JointState:=match i with
  | .inl p=>(LeftFrozenFiniteHaarFunctional.functional (ha p.1) (hell p.1) (hb p.1)
      n (min p.2 H) (z.1 p.1,z.2 p.1),0)
  | .inr p=>(0,z.2 p.1 p.2.1 p.2.2)

include hβ hHolder hholder in
theorem encoded_measurable(n:ℕ)(i:Tag):Measurable (encoded H a ha ell M hell hb n i):=by
  cases i with
  | inl p=>
    have hs:Measurable (fun z:Source=>(z.1 p.1,z.2 p.1)):=
      ((measurable_pi_apply p.1).comp measurable_fst).prodMk
        ((measurable_pi_apply p.1).comp measurable_snd)
    exact ((LeftFrozenFiniteHaarFunctional.functional_measurable (ha p.1) (hell p.1) (hb p.1)
      hβ (hHolder p.1) (hholder p.1) n (min p.2 H)).comp hs).prodMk measurable_const
  | inr p=>
    have he:Measurable (fun z:Source=>z.2 p.1 p.2.1 p.2.2):=
      (measurable_pi_apply p.2.2).comp ((measurable_pi_apply p.2.1).comp
        ((measurable_pi_apply p.1).comp measurable_snd))
    exact measurable_const.prodMk he

include hUa in
theorem source_measurable:Measurable (source 𝓕 μ H U J):=
  (measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr
    (fun t=>((hUa b t).mono (𝓕.le t)).measurable))).prodMk
    (measurable_pi_iff.mpr (fun b=>measurable_pi_iff.mpr
      (fun i=>measurable_pi_iff.mpr (fun t=>LeftFrozenConvolutionLaw.driver_measurable 𝓕 μ H (J b) i t))))

theorem process_measurable(i:Tag):Measurable
    (process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i):=by
  cases i with
  | inl p=>exact (Lp.stronglyMeasurable _).measurable.prodMk measurable_const
  | inr p=>exact measurable_const.prodMk (LeftFrozenConvolutionLaw.driver_measurable 𝓕 μ H (J p.1) p.2.1 p.2.2)

variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
include hLip hIJ hlocal in
theorem encoded_in_measure(i:Tag):
    TendstoInMeasure μ
      (fun n ω=>encoded H a ha ell M hell hb n i (source 𝓕 μ H U J ω)) atTop
      (process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i):=by
  have hs:=source_measurable 𝓕 μ H U hUa J
  cases i with
  | inr p=>
    apply tendstoInMeasure_of_tendsto_ae
      (fun n=>((encoded_measurable H a ha ell M Holder hell hb β hβ hHolder hholder n (.inr p)).comp hs).aestronglyMeasurable)
    exact ae_of_all _ (fun _=>tendsto_const_nhds)
  | inl p=>
    have hh:=LeftFrozenConvolutionLaw.in_measure 𝓕 μ H hH (ha p.1) (hell p.1) (hb p.1)
      hβ (hHolder p.1) (hholder p.1) (U p.1) (hUa p.1) (hc p.1) (hLip p.1)
      (I p.1) (J p.1) (hIJ p.1) (hlocal p.1) (min p.2 H) (min_le_right _ _)
    have hm(n:ℕ):Measurable (LeftFrozenFiniteHaarIntegral.value (ha p.1) (hell p.1) (hb p.1)
      (U p.1) n (min p.2 H) (driver 𝓕 μ H J p.1)):=by
      have hproj:Measurable (fun z:Source=>(z.1 p.1,z.2 p.1)):=
        ((measurable_pi_apply p.1).comp measurable_fst).prodMk
          ((measurable_pi_apply p.1).comp measurable_snd)
      simpa only [Function.comp_def,source,driver,LeftFrozenFiniteHaarFunctional.functional_eval] using
        (LeftFrozenFiniteHaarFunctional.functional_measurable (ha p.1) (hell p.1) (hb p.1)
          hβ (hHolder p.1) (hholder p.1) n (min p.2 H)).comp (hproj.comp hs)
    have hz:TendstoInMeasure μ (fun _:ℕ=>fun _:Ω=>(0:ℝ)) atTop (fun _=>0):=
      tendstoInMeasure_of_tendsto_ae (fun _=>aestronglyMeasurable_const)
        (ae_of_all _ (fun _=>tendsto_const_nhds))
    have hp:=FiniteJointProbabilityLimit.prod μ _ _ _ _
      (fun n=>(hm n).aestronglyMeasurable) (fun _=>aestronglyMeasurable_const) hh hz
    have heproc:process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J (.inl p)=
        (fun ω=>(convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I p.1 p.2 ω,0)):=rfl
    rw [heproc]
    change TendstoInMeasure μ _ atTop (fun ω=>(convolution 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I p.1 p.2 ω,0)) at hp
    simpa only [encoded,source,driver,LeftFrozenFiniteHaarFunctional.functional_eval] using hp

variable {Ω':Type*}[MeasurableSpace Ω']
include hLip hIJ hlocal in
/-- Both original convolutions and both original cylindrical drivers
retain their full joint law across spaces. The convergence premises
are proved from actual heat-Haar finite sums, not supplied externally. -/
theorem joint_law(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (V:Bool→ℝ≥0→Ω'→StateL2)(hVa:∀b,StronglyAdapted 𝓖 (V b))(hVc:∀b ω,Continuous (fun t=>V b t ω))
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (hLaw:μ.map (source 𝓕 μ H U J)=ν.map (source 𝓖 ν H V J')):
    μ.map (fun ω=>fun i:Tag=>process 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J i ω)=
      ν.map (fun ω=>fun i:Tag=>process 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J' i ω):=by
  exact CylindricalFunctionalLawLimit.law μ ν (source 𝓕 μ H U J) (source 𝓖 ν H V J')
    (source_measurable 𝓕 μ H U hUa J) (source_measurable 𝓖 ν H V hVa J') hLaw
    (encoded H a ha ell M hell hb) (encoded_measurable H a ha ell M Holder hell hb β hβ hHolder hholder)
    _ _ (process_measurable 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc I J)
    (process_measurable 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc I' J')
    (encoded_in_measure 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder U hUa hc L hLip I J hIJ hlocal)
    (encoded_in_measure 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder V hVa hVc L hLip I' J' hIJ' hlocal')
end SHE.TwoChannelConvolutionLaw
