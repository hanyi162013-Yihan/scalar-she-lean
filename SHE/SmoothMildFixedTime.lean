module
public import SHE.SmoothPicardCommonLaw
public import SHE.SmoothMildExistence
public import SHE.FixedHorizonPicard
public import SHE.ContinuousDampedForced
public import SHE.HaarPredictableVersion
public import SHE.DampedConvolutionZero
public import SHE.PredictableClock
public import SHE.HeatInitialProcess
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.SmoothMildFixedTime
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

variable(I:Bool→StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable(B:Bool→ℝ≥0)(hBDG:∀b,StandardTerminalBDG16 (I b) (B b))
variable(hpos:0<H)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable(z:ℝ≥0→StateL2)(hz:Continuous z)
local notation "N"=>NonlinearConvolution.map 𝓕 μ H (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)
local notation "Add"=>NonlinearConvolution.map 𝓕 μ H (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true) (I true) (0:Process (E:=StateL2) 𝓕 μ H)

include hH hBDG hpos hnull hz in
/-- An actual smooth solution on the prescribed full horizon. The
Lipschitz constant changes only the Bielecki weight, not the interval.
The returned bundle retains the fixed-point equation used by common law. -/
theorem exists_mild_equation {L:ℝ≥0}(hLip:LipschitzWith L (fun x=>(a false x:ℂ)))
    (Z:Process (E:=StateL2) 𝓕 μ H)
    (hZ:(fun p:ℝ≥0×Ω=>z p.1)=ᵐ[energyMeasure μ H] Z):
    ∃A:SmoothPicardCommonLaw.Mild 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I z,
      A.deterministic=Z ∧ StronglyMeasurable[𝓕.predictable] (Function.uncurry A.value) ∧
      ∃hfield:StronglyMeasurable[𝓕.predictable]
          (ContinuousHeatMild.coefficientFunction (ha false) (hell false) (hb false) A.value),
        ∀(t:ℝ≥0)(ht:t≤H),A.value t=ᵐ[μ] fun ω=>z t+
          DampedFixedIntegral.value 𝓕 μ H hH (Λ:=0) (by norm_num) (hell true)
            ((hell true).le.trans ((hb true 0).1.trans (hb true 0).2))
            (NonlinearConvolution.field 𝓕 μ H (ha true) (hell true) (hb true) 0)
            (NonlinearConvolution.field_predictable 𝓕 μ H (ha true) (hell true) (hb true)
              hβ (hHolder true) (hholder true) 0) (I true) t ht ω+
          DampedFixedIntegral.value 𝓕 μ H hH (Λ:=0) (by norm_num) (hell false)
            ((hell false).le.trans ((hb false 0).1.trans (hb false 0).2))
            (ContinuousHeatMild.coefficientFunction (ha false) (hell false) (hb false) A.value)
            hfield (I false) t ht ω := by
  let f:=NonlinearConvolution.field 𝓕 μ H (ha true) (hell true) (hb true)
    (0:Process (E:=StateL2) 𝓕 μ H)
  have hf:StronglyMeasurable[𝓕.predictable] f:=NonlinearConvolution.field_predictable
    𝓕 μ H (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true) 0
  have hM:0≤M true:=(hell true).le.trans ((hb true 0).1.trans (hb true 0).2)
  let Y:=DampedContinuousVersion.version 𝓕 μ H hH (Λ:=0) (by norm_num) (hell true) hM f hf (I true)
  have hYc:∀ω,Continuous (fun t=>Y t ω):=DampedContinuousVersion.continuous_version
    𝓕 μ H hH (Λ:=0) (by norm_num) (hell true) hM f hf (I true) hpos
  have hYp:StronglyMeasurable[𝓕.predictable] (Function.uncurry Y):=
    DampedPredictableVersion.predictable_version 𝓕 μ H hH (Λ:=0) (by norm_num) (hell true) hM f hf (I true)
      (B true) (hBDG true) hnull hpos
  have hYa:Add=ᵐ[energyMeasure μ H] Function.uncurry Y:=by
    rw [←DampedConvolutionZero.nonlinear 𝓕 μ H (hell true) (ha true) (hb true)
      hβ (hHolder true) (hholder true) hH (I true) 0]
    exact DampedPredictableVersion.convolution_ae_version 𝓕 μ H hH (Λ:=0) (by norm_num)
      (hell true) hM f hf (I true) (B true) (hBDG true) hpos
  let F:ℝ≥0→Ω→StateL2:=fun t ω=>z t+Y t ω
  have hFc:∀ω,Continuous (fun t=>F t ω):=fun ω=>hz.add (hYc ω)
  have hzp:StronglyMeasurable[𝓕.predictable] (fun p:ℝ≥0×Ω=>z p.1):=
    (hz.measurable.comp (PredictableClock.time_measurable 𝓕)).stronglyMeasurable
  have hFp:StronglyMeasurable[𝓕.predictable] (Function.uncurry F):=hzp.add hYp
  let w:=Z+Add
  have hw:w=ᵐ[energyMeasure μ H] Function.uncurry F:=by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_add Z Add),hZ,hYa] with p hp hzq hyq
    change w p=F p.1 p.2
    rw [hp]
    change Z p+Add p=F p.1 p.2
    rw [←hzq,hyq]
    rfl
  obtain ⟨v,hv,_⟩:=FixedHorizonPicard.exists_unique_forced 𝓕 μ H hH (Λ:=0) (by norm_num)
    (ha false) (hell false) (hb false) hβ (hHolder false) (hholder false) (I false)
    (B false) (hBDG false) hpos hLip w
  obtain ⟨V,hVc,hVp,hVv,hfield,hmild⟩:=ContinuousDampedForced.continuous_representative
    𝓕 μ H hH (Λ:=0) (by norm_num) (ha false) (hell false) (hb false) hβ
    (hHolder false) (hholder false) (I false) hpos hnull (B false) (hBDG false)
    F hFc hFp w hw v hv
  have hv':v=Z+Add+N v:=by
    rw [DampedConvolutionZero.nonlinear 𝓕 μ H (hell false) (ha false) (hb false)
      hβ (hHolder false) (hholder false) hH (I false)] at hv
    exact hv
  let A:SmoothPicardCommonLaw.Mild 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I z:=
    ⟨Z,v,hZ,hv',V,hVc,(hVp.mono (predictable_le_product 𝓕)).measurable,hVv.symm⟩
  refine ⟨A,rfl,hVp,hfield,?_⟩
  intro t ht
  filter_upwards [hmild t ht,
    DampedContinuousVersion.version_ae_of_le 𝓕 μ H hH (Λ:=0) (by norm_num)
      (hell true) hM f hf (I true) (B true) (hBDG true) hpos t ht] with ω hω hY
  change V t ω=F t ω+_ at hω
  change Y t ω=_ at hY
  change V t ω=_
  dsimp only [F] at hω
  rw [hY] at hω
  exact hω
end SHE.SmoothMildFixedTime
