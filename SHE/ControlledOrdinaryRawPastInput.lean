module
public import SHE.ControlledOrdinaryPastInput
public import SHE.ControlledOrdinaryPhysicalSections
public import SHE.OrdinaryNativePhysicalInput
public import SHE.PastParameterRawLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.ControlledOrdinaryRawPastInput
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance controlledOrdinaryRawPastInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledOrdinaryRawPastInput_sigma:MeasurableSpace CircleL2:=borel _
local instance controlledOrdinaryRawPastInput_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance controlledOrdinaryRawPastInput_secondCountable:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance controlledOrdinaryRawPastInput_realSigma:MeasurableSpace RealL2:=borel _
local instance controlledOrdinaryRawPastInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance controlledOrdinaryRawPastInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance controlledOrdinaryRawPastInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance controlledOrdinaryRawPastInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance controlledOrdinaryRawPastInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(A:ℝ→ℝ)(hA:BoundedSmooth A)
variable (Λ θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (Z:VariableObservations.Family HeatCircle 1)
variable (hstop:∀x,(Z.observations x 0).stop=(b:ℝ))(htarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z ht hs F hF hFm
local notation "R₀"=>referenceData P A hA Λ θ v b hvb (0,0)
variable {Ω:Type}[MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable (ν:Measure HeatCircle)[IsFiniteMeasure ν]
variable (c:ℝ≥0)(hν:ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))

include hstop htarget hcenter hν in
theorem fixed_input(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)(p:Inputs)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫h,OrdinaryUncutPhysicalGradient.raw m (Base p) k (h,z) ∂historyMeasure R₀ ν k)∧
      m.scalarIto.integral input=ᵐ[μ] ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k:=by
  obtain ⟨input,hi,hout⟩:=OrdinaryNativePhysicalInput.original_input (Base p) m (b:ℝ)
    (fun _=>rfl) hstop htarget hcenter ν c hν (by exact_mod_cast hbH) hb1 (by exact_mod_cast hvb') k
  have he:=ControlledOrdinaryAverage.measure_eq P A hA Λ θ v b hvb ν p (0,0) k
  rw [he] at hi hout
  refine ⟨input,hi,?_⟩
  filter_upwards [hout] with ω hω
  change m.scalarIto.integral input ω=∫h,OrdinaryUncutNoise.value m (Base p) k h ω ∂historyMeasure R₀ ν k
  exact hω

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hstop htarget hcenter hν hsmall in
/-- Genuine past substitution retains BOTH the original J output and
its literal native ordinary-U gradient input. No restart, conditional
Gaussian law or fixed-reference exceptional set is supplied. -/
theorem random_input(hlocal:StandardTerminalPastLocality m.scalarIto)(hΛ:0≤Λ)
    (hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)(u:Ω→Inputs)(hu:StronglyMeasurable[𝓕 v] u)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>∫h,OrdinaryUncutPhysicalGradient.raw m (Base (u z.2)) k (h,z) ∂historyMeasure R₀ ν k)∧
      m.scalarIto.integral input=ᵐ[μ] fun ω=>ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν (u ω) k ω:=by
  let g:=fun p:Inputs=>fun z:ℝ≥0×Ω=>∫h,OrdinaryUncutPhysicalGradient.raw m (Base p) k (h,z) ∂historyMeasure R₀ ν k
  let K:=fun p:Inputs=>fun ω=>ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k ω
  have hc:∀ᵐz∂energyMeasure μ H,Continuous (fun p=>g p z):=
    ControlledOrdinaryPhysicalSections.average_parameter_continuous P A hA Λ θ v b hvb Z ht hs F hF hFm
      m k hsmall hΛ hbH hb1 ν
  have hz(p:Inputs)(z:ℝ≥0×Ω)(hq:z.1≤v):g p z=0:=by
    apply integral_eq_zero_of_ae
    filter_upwards with h
    have hn:¬((referenceData P A hA Λ θ v b hvb p).base<(z.1:ℝ)∧
        (z.1:ℝ)<(UncutWordEvaluation.normalizedLevel (Base p) k).terminal h):=by
      intro htimes
      have hle:(z.1:ℝ)≤(v:ℝ):=by exact_mod_cast hq
      exact (not_lt_of_ge hle) htimes.1
    simp only [OrdinaryUncutPhysicalGradient.raw,OrdinaryPhysicalGradient.raw,if_neg hn,smul_zero,Pi.zero_apply]
  obtain ⟨B,hB,hBb⟩:=ControlledOrdinaryAverage.average_bound P A hA Λ θ v b hvb Z ht hs F hF hFm m ν k
  exact PastParameterRawLimit.original_input 𝓕 μ H v m.scalarIto hlocal g hc hz K
    (fun p=>ControlledOrdinaryAverage.average_measurable P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k)
    (fun ω=>ControlledOrdinaryAverage.average_continuous P A hA Λ θ v b hvb Z ht hs F hF hFm m hsmall hΛ ν k ω)
    hB hBb (fun p=>fixed_input P A hA Λ θ v b hvb Z hstop htarget hcenter F hF hFm m ν c hν hbH hb1 hvb' p k) hu

end SHE.ControlledOrdinaryRawPastInput
