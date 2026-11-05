module
public import SHE.ControlledOrdinaryAverage
public import SHE.OrdinaryNativeOriginalInput
public import SHE.PastParameterOriginalIto

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
namespace SHE.ControlledOrdinaryPastInput
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
open scoped NNReal ENNReal
local instance controlledOrdinaryPastInput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledOrdinaryPastInput_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledOrdinaryPastInput_borel : BorelSpace CircleL2 := ⟨rfl⟩
local instance controlledOrdinaryPastInput_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance controlledOrdinaryPastInput_realSigma : MeasurableSpace RealL2 := borel _
local instance controlledOrdinaryPastInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance controlledOrdinaryPastInput_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance controlledOrdinaryPastInput_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance controlledOrdinaryPastInput_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance controlledOrdinaryPastInput_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (hstop : ∀x,(Z.observations x 0).stop=(b:ℝ))
variable (htarget : ∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter : ∀x,(Z.observations x 0).center=x)
local notation "ht" => (fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs" => (fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1 => F q.1 q.2))
local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z ht hs F hF hFm
variable {Ω : Type} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {H : ℝ≥0} {κ : ℝ} {a : ℝ→ℝ} {ell M : ℝ}
variable (m : TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable (ν : Measure HeatCircle) [IsFiniteMeasure ν]
variable (c : ℝ≥0) (hν : ν≤(c:ℝ≥0∞) • (AddCircle.haarAddCircle:Measure HeatCircle))

include hstop htarget hcenter hν in
theorem fixed_input (hlocal : StandardTerminalPastLocality m.scalarIto) (hbH : b≤H)
    (hvb' : v<b) (p : Inputs) (k : ℕ) :
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input)=ᵐ[μ]
        ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k := by
  have hx:=OrdinaryNativeOriginalInput.original_post_input (Base p) m (b:ℝ)
    (fun _=>rfl) hstop htarget hcenter ν c hν hlocal v rfl (by exact_mod_cast hbH)
    (by exact_mod_cast hvb') k
  obtain ⟨input,hinput⟩:=hx
  refine ⟨input,?_⟩
  have he:=ControlledOrdinaryAverage.measure_eq P A hA Λ θ v b hvb ν p (0,0) k
  rw [he] at hinput
  filter_upwards [hinput] with ω hω
  change m.scalarIto.integral (PastItoInputs.post 𝓕 μ H v input) ω=
    ∫h,OrdinaryUncutNoise.value m (Base p) k h ω
      ∂historyMeasure (referenceData P A hA Λ θ v b hvb (0,0)) ν k
  exact hω

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hstop htarget hcenter hν hsmall in
/-- The actual ordinary-U uncut noise at an F_v-random controlled
reference is an integral against the SAME original scalar driver.
Both recursive cutoffs and the native root heat gap are already gone. -/
theorem random_input (hlocal : StandardTerminalPastLocality m.scalarIto) (hΛ : 0≤Λ)
    (hbH : b≤H) (hvb' : v<b) (u : Ω→Inputs) (hu : StronglyMeasurable[𝓕 v] u) (k : ℕ) :
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      m.scalarIto.integral input=ᵐ[μ] fun ω=>
        ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν (u ω) k ω := by
  obtain ⟨B,hB,hBb⟩:=ControlledOrdinaryAverage.average_bound P A hA Λ θ v b hvb Z ht hs F hF hFm m ν k
  exact PastParameterOriginalIto.random_input 𝓕 μ H v m.scalarIto hlocal
    (fun p ω=>ControlledOrdinaryAverage.average P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k ω)
    (fun p=>ControlledOrdinaryAverage.average_measurable P A hA Λ θ v b hvb Z ht hs F hF hFm m ν p k)
    (fun ω=>ControlledOrdinaryAverage.average_continuous P A hA Λ θ v b hvb Z ht hs F hF hFm m hsmall hΛ ν k ω)
    hB hBb (fun p=>fixed_input P A hA Λ θ v b hvb Z hstop htarget hcenter F hF hFm m ν c hν
      hlocal hbH hvb' p k) hu

end SHE.ControlledOrdinaryPastInput
