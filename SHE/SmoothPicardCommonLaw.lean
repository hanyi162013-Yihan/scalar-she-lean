module
public import SHE.ContinuousPicardClass
public import SHE.ContinuousPicardIterates
public import SHE.ContinuousPicardLimitLaw
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.SmoothPicardCommonLaw
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



local notation "N"=>NonlinearConvolution.map 𝓕 μ H (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)
local notation "Add"=>NonlinearConvolution.map 𝓕 μ H (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true) (I true) (0:Process (E:=StateL2) 𝓕 μ H)

def process(Z:Process (E:=StateL2) 𝓕 μ H)(n:ℕ):Process (E:=StateL2) 𝓕 μ H:=
  (fun w=>Z+Add+N w)^[n] 0
local notation "ProcessN"=>process 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I
variable (hz:Continuous z)
local notation "PathN"=>ContinuousPicardIterates.iterate
  𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull z hz


structure Mild where
  deterministic:Process (E:=StateL2) 𝓕 μ H
  state:Process (E:=StateL2) 𝓕 μ H
  deterministic_ae:(fun p:ℝ≥0×Ω=>z p.1)=ᵐ[energyMeasure μ H] deterministic
  fixed:state=deterministic+Add+N state
  value:ℝ≥0→Ω→StateL2
  continuous:∀ω,Continuous (fun t=>value t ω)
  measurable:Measurable (Function.uncurry value)
  version:Function.uncurry value=ᵐ[energyMeasure μ H] state

variable(hIJ:∀b,NativeObservationNaturality.StandardScalarNaturality (I b) (J b))
variable(hlocal:∀b,StandardTerminalPastLocality (J b))
variable {Ω':Type*}[MeasurableSpace Ω']
include hH hz hLip hIJ hlocal hBDG hpos hnull in
/-- Actual smooth stochastic fixed points on unrelated spaces have
one continuous-path law. The stochastic Picard approximation, its joint
driver law induction, and ordinary product-L2 convergence are proved
internally; no smooth SPDE common-law hypothesis is used. -/
theorem paths
    (A:Mild 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I z)
    (𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ω'›)(ν:Measure Ω')[IsProbabilityMeasure ν]
    (I':Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓖 ν H)
    (J':Bool→StandardTerminalIto (C:=FiniteHaar.RealHaarInput) (E:=ℝ) 𝓖 ν H)
    (hBDG':∀b,StandardTerminalBDG16 (I' b) (B b))
    (hnull':NullCompleteFiltration.ContainsNullSets 𝓖 ν)
    (hIJ':∀b,NativeObservationNaturality.StandardScalarNaturality (I' b) (J' b))
    (hlocal':∀b,StandardTerminalPastLocality (J' b))
    (A':Mild 𝓖 ν H a ha ell M Holder hell hb β hβ hHolder hholder I' z)
    (hDriver:μ.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓕 μ H J b i t ω)=
      ν.map (fun ω=>fun b i t=>TwoChannelConvolutionLaw.driver 𝓖 ν H J' b i t ω)):
    NativePathLawComparison.law H μ A.value A.continuous=
      NativePathLawComparison.law H ν A'.value A'.continuous:=by
  let PX:ℕ→ContinuousPicardIterates.Paths 𝓕:=PathN
  let PY:ℕ→ContinuousPicardIterates.Paths 𝓖:=ContinuousPicardIterates.iterate
    𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder I' B hBDG' hpos hnull' z hz
  let X:ℕ→Bool→ℝ≥0→Ω→StateL2:=fun n=>(PX n).value
  let Y:ℕ→Bool→ℝ≥0→Ω'→StateL2:=fun n=>(PY n).value
  have hxa:∀n b,StronglyAdapted 𝓕 (X n b):=fun n=>(PX n).adapted
  have hya:∀n b,StronglyAdapted 𝓖 (Y n b):=fun n=>(PY n).adapted
  have hxc:∀n b ω,Continuous (fun t=>X n b t ω):=fun n=>(PX n).continuous
  have hyc:∀n b ω,Continuous (fun t=>Y n b t ω):=fun n=>(PY n).continuous
  have hx0:X 0=(fun _ _ _=>0):=by dsimp only [X,PX];rw [ContinuousPicardIterates.iterate_zero];rfl
  have hy0:Y 0=(fun _ _ _=>0):=by dsimp only [Y,PY];rw [ContinuousPicardIterates.iterate_zero];rfl
  have hxs:∀n,X (n+1)=ContinuousPicardStepLaw.step 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder
      (X n) (hxa n) (hxc n) I z:=by
    intro n
    dsimp only [X,PX]
    rw [ContinuousPicardIterates.iterate_succ]
    rfl
  have hys:∀n,Y (n+1)=ContinuousPicardStepLaw.step 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder
      (Y n) (hya n) (hyc n) I' z:=by
    intro n
    dsimp only [Y,PY]
    rw [ContinuousPicardIterates.iterate_succ]
    rfl
  have hlaw:=ContinuousPicardIterates.law_of_recursion 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder
    L hLip I J B hBDG hpos z hIJ hlocal hz 𝓖 ν I' J' hBDG' hnull' hIJ' hlocal' hDriver
    X hxa hxc Y hya hyc hx0 hy0 hxs hys
  have hlawFalse:∀n,μ.map (fun ω=>fun t=>X n false t ω)=ν.map (fun ω=>fun t=>Y n false t ω):=by
    intro n
    let dec:TwoChannelConvolutionLaw.Source→(ℝ≥0→StateL2):=fun w=>w.1 false
    have hm:Measurable dec:=(measurable_pi_apply false).comp measurable_fst
    have he:=congrArg (fun P:Measure TwoChannelConvolutionLaw.Source=>P.map dec) (hlaw n)
    rw [Measure.map_map hm (TwoChannelConvolutionLaw.source_measurable 𝓕 μ H (X n) (hxa n) J),
      Measure.map_map hm (TwoChannelConvolutionLaw.source_measurable 𝓖 ν H (Y n) (hya n) J')] at he
    exact he
  have hxm:∀n,Measurable (Function.uncurry (X n false)):=fun n=>
    ((ContinuousPredictable.stronglyMeasurable 𝓕 (X n false) (hxa n false) (hxc n false)).mono
      (predictable_le_product 𝓕)).measurable
  have hym:∀n,Measurable (Function.uncurry (Y n false)):=fun n=>
    ((ContinuousPredictable.stronglyMeasurable 𝓖 (Y n false) (hya n false) (hyc n false)).mono
      (predictable_le_product 𝓖)).measurable
  have he:=ContinuousPicardClass.energy_limit 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder
    I B hBDG hpos hnull z hz (hLip false) A.deterministic A.state A.deterministic_ae A.fixed A.value A.version
  have hf:=ContinuousPicardClass.energy_limit 𝓖 ν H hH a ha ell M Holder hell hb β hβ hHolder hholder
    I' B hBDG' hpos hnull' z hz (hLip false) A'.deterministic A'.state A'.deterministic_ae A'.fixed A'.value A'.version
  apply ContinuousPicardLimitLaw.paths H hpos μ ν A.value A'.value A.continuous A'.continuous A.measurable A'.measurable
    (fun n=>X n false) (fun n=>Y n false) (fun n=>hxc n false) (fun n=>hyc n false) hxm hym hlawFalse
  · intro n
    apply (he.1 n).congr
    exact ae_of_all _ (fun q=>congrArg (fun r:ℝ=>r^2)
      (norm_sub_rev (X n false q.1 q.2) (A.value q.1 q.2)))
  · intro n
    apply (hf.1 n).congr
    exact ae_of_all _ (fun q=>congrArg (fun r:ℝ=>r^2)
      (norm_sub_rev (Y n false q.1 q.2) (A'.value q.1 q.2)))
  · apply he.2.congr'
    exact Filter.Eventually.of_forall (fun n=>integral_congr_ae (ae_of_all _
      (fun q=>congrArg (fun r:ℝ=>r^2) (norm_sub_rev (X n false q.1 q.2) (A.value q.1 q.2)))))
  · apply hf.2.congr'
    exact Filter.Eventually.of_forall (fun n=>integral_congr_ae (ae_of_all _
      (fun q=>congrArg (fun r:ℝ=>r^2) (norm_sub_rev (Y n false q.1 q.2) (A'.value q.1 q.2)))))
end SHE.SmoothPicardCommonLaw
