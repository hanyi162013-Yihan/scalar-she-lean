module
public import SHE.SmoothPicardCommonLaw
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
namespace SHE.SmoothMildExistence
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
theorem exists_mild {L:ℝ≥0}(hLip:LipschitzWith L (fun x=>(a false x:ℂ)))
    (Z:Process (E:=StateL2) 𝓕 μ H)
    (hZ:(fun p:ℝ≥0×Ω=>z p.1)=ᵐ[energyMeasure μ H] Z):
    ∃A:SmoothPicardCommonLaw.Mild 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I z,
      A.deterministic=Z ∧ StronglyMeasurable[𝓕.predictable] (Function.uncurry A.value) := by
  let f:=NonlinearConvolution.field 𝓕 μ H (ha true) (hell true) (hb true)
    (0:Process (E:=StateL2) 𝓕 μ H)
  have hf:StronglyMeasurable[𝓕.predictable] f:=NonlinearConvolution.field_predictable
    𝓕 μ H (ha true) (hell true) (hb true) hβ (hHolder true) (hholder true) 0
  have hM:0≤M true:=(hell true).le.trans ((hb true 0).1.trans (hb true 0).2)
  let Y:=HaarContinuousVersion.version 𝓕 μ H hH (hell true) hM f hf (I true)
  have hYc:∀ω,Continuous (fun t=>Y t ω):=HaarContinuousVersion.continuous_version
    𝓕 μ H hH (hell true) hM f hf (I true) hpos
  have hYp:StronglyMeasurable[𝓕.predictable] (Function.uncurry Y):=
    HaarPredictableVersion.predictable_version 𝓕 μ H hH (hell true) hM f hf (I true)
      (B true) (hBDG true) hnull hpos
  have hYa:Add=ᵐ[energyMeasure μ H] Function.uncurry Y:=
    HaarPredictableVersion.convolution_ae_version 𝓕 μ H hH (hell true) hM f hf (I true)
      (B true) (hBDG true) hpos
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
  exact ⟨⟨Z,v,hZ,hv',V,hVc,(hVp.mono (predictable_le_product 𝓕)).measurable,hVv.symm⟩,rfl,hVp⟩

include hH hBDG hpos hnull in
/-- The actual deterministic heat initial condition supplies the
required predictable process on every fixed interval. -/
theorem exists_heat_mild {L:ℝ≥0}(hLip:LipschitzWith L (fun x=>(a false x:ℂ)))
    (u₀:StateL2):
    ∃A:SmoothPicardCommonLaw.Mild 𝓕 μ H a ha ell M Holder hell hb β hβ hHolder hholder I
        (fun t=>RealHeat.realHeat (t:ℝ) u₀),
      A.deterministic=HeatInitialProcess.process 𝓕 μ H u₀ ∧
        StronglyMeasurable[𝓕.predictable] (Function.uncurry A.value) := by
  have hp:Continuous (fun t:ℝ≥0=>((t:ℝ),u₀)):=continuous_subtype_val.prodMk continuous_const
  have hz:=RealHeat.continuous_realHeat_action.comp hp
  change Continuous (fun t:ℝ≥0=>RealHeat.realHeat (t:ℝ) u₀) at hz
  exact exists_mild 𝓕 μ H hH a ha ell M Holder hell hb β hβ hHolder hholder I B hBDG hpos hnull
    (fun t=>RealHeat.realHeat (t:ℝ) u₀) hz hLip (HeatInitialProcess.process 𝓕 μ H u₀)
    (HeatInitialProcess.process_ae 𝓕 μ H u₀).symm
end SHE.SmoothMildExistence
