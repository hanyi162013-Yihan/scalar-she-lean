module

public import SHE.MixedCanonicalUncutPhysicalInput
public import SHE.MixedCanonicalWeightedPhysicalCoordinates
public import SHE.MixedCanonicalRootOriginalIto
public import SHE.NativeBesselDifferenceIdentity
public import SHE.RootDensityHistory
public import SHE.MixedCanonicalPhysicalCoordinates
public import SHE.NativeScalarFourierWeight
public import SHE.MixedUncutPhysicalColumns
public import SHE.ScalarRootUncutPhysicalInput
public import SHE.MixedCanonicalPhysicalSections
public import SHE.PastParameterRawLimit
public import SHE.MixedCanonicalUncutOriginalNoise
public import SHE.ControlledReferenceFamilyResidual
public import SHE.PastParameterOriginalIto
public import SHE.PastItoLimitWitness
public import SHE.HistoryMeasureGeometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalNoiseIncrement
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalPhysicalCoordinates_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : HeatCircle×WordRecursion.State 1 => F q.1 q.2))


local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

open Filter Topology
local notation "Base" => ControlledReferenceFamilyLevel.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF hFm

open CutoffWordHistories
local notation "LS" => ControlledReferenceFamilySections.leafSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "RS" => ControlledReferenceFamilySections.referenceSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "MS" => ControlledReferenceFamilySections.markSection 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P hAs θ v b hvb Z htarget hstop F hF hFm

local notation "K" => ControlledReferenceFamilyResidual.residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "N" => (fun p:Inputs=>MixedUncutSampleExpansion.noiseMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p))

local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "Raw"=>(fun k p=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Base p) k)

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)


local notation "Noise"=>MixedCanonicalWeightedPhysicalCoordinates.noise
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "D"=>MixedCanonicalRootFields.residual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm
local notation "Cumulative"=>MixedCanonicalRootOriginalIto.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

def field(k:ℕ)(z:Ω×HeatCircle):ℝ:=RootSectionAverage.average R₀ k (Noise k) z
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

def value(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(ω:Ω):CircleL2:=
  Cumulative hL hρ (k+1) ω-Cumulative hL hρ k ω
local notation "Value"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall in
/-- The actual kth root-retained noise is precisely the increment of
cumulative finite stochastic residuals, pointwise in the actual past. -/
theorem cycle(hΛ:0≤Λ)(k:ℕ)(ω:Ω)(x:HeatCircle):
    Field k (ω,x)=D (k+1) (ω,x)-D k (ω,x):=by
  have hd(m:ℕ):D m (ω,x)=K (Measure.dirac x) m (pastParameter ω) ω:=by
    simpa only [integral_dirac] using MixedCanonicalRootFields.residual_integral
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ (Measure.dirac x) m ω
  have hi:=MixedCanonicalWeightedPhysicalCoordinates.noise_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hΛ (Measure.dirac x) k ω
  have hr:=RootSectionAverage.integral_dirac_history R₀ k x (fun h=>Noise k (ω,h)) hi
  calc
    _ = ∫h,Noise k (ω,h) ∂historyMeasure R₀ (Measure.dirac x) k:=hr.symm
    _ = K (Measure.dirac x) (k+1) (pastParameter ω) ω-K (Measure.dirac x) k (pastParameter ω) ω:=
      (MixedCanonicalUncutPhysicalInput.residual_difference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hΛ (Measure.dirac x) k (pastParameter ω) ω).symm
    _ = _:=by rw [←hd (k+1),←hd k]

include hsmall in
theorem field_measurable(hΛ:0≤Λ)(k:ℕ):Measurable (Field k):=by
  have hn:=MixedCanonicalRootFields.residual_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ (k+1)
  have hk:=MixedCanonicalRootFields.residual_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k
  convert! hn.sub hk using 1
  funext z
  exact cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k z.1 z.2

include hsmall in
theorem section_memLp(hΛ:0≤Λ)(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>Field k (ω,x)) 2 AddCircle.haarAddCircle:=by
  have hn:=MixedCanonicalRootOriginalIto.section_memLp
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ (k+1) ω
  have hk:=MixedCanonicalRootOriginalIto.section_memLp
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k ω
  have he:(fun x:HeatCircle=>Field k (ω,x))=ᵐ[AddCircle.haarAddCircle]
      (fun x=>D (k+1) (ω,x)-D k (ω,x)):=ae_of_all _ (fun x=>
    cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hΛ k ω x)
  exact (memLp_congr_ae he).mpr (hn.sub hk)

include hsmall in
theorem value_measurable(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ):Measurable (Value hL hρ k):=
  (MixedCanonicalRootOriginalIto.value_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ (k+1)).sub
  (MixedCanonicalRootOriginalIto.value_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ k)

include hsmall in
/-- This individual Hilbert noise is the native realization of the
literal retained-root kth scalar noise, without a version hypothesis. -/
theorem value_eq_native(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(ω:Ω):
    Value hL hρ k ω=NativeBesselFieldAE.value Λ ρ hL hρ
      (fun z:Ω×HeatCircle=>(Field k z:ℂ)) ω:=by
  let A:=fun z:Ω×HeatCircle=>(Field k z:ℂ)
  let B:=fun z:Ω×HeatCircle=>(D (k+1) z:ℂ)
  let C:=fun z:Ω×HeatCircle=>(D k z:ℂ)
  have hA:Measurable A:=Complex.continuous_ofReal.measurable.comp
    (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k)
  have hB:Measurable B:=Complex.continuous_ofReal.measurable.comp
    (MixedCanonicalRootFields.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) (k+1))
  have hC:Measurable C:=Complex.continuous_ofReal.measurable.comp
    (MixedCanonicalRootFields.residual_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k)
  have hpA:MemLp (fun x=>A (ω,x)) 2 AddCircle.haarAddCircle:=
    (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k ω).ofReal
  have hpB:MemLp (fun x=>B (ω,x)) 2 AddCircle.haarAddCircle:=
    (MixedCanonicalRootOriginalIto.section_memLp
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) (k+1) ω).ofReal
  have hpC:MemLp (fun x=>C (ω,x)) 2 AddCircle.haarAddCircle:=
    (MixedCanonicalRootOriginalIto.section_memLp
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k ω).ofReal
  have he:∀ᵐx∂AddCircle.haarAddCircle,A (ω,x)=B (ω,x)-C (ω,x):=by
    apply ae_of_all
    intro x
    change (Field k (ω,x):ℂ)=(D (k+1) (ω,x):ℂ)-(D k (ω,x):ℂ)
    rw [cycle 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k ω x]
    exact Complex.ofReal_sub _ _
  exact (NativeBesselDifferenceIdentity.sub Λ ρ hL hρ A B C hA hB hC ω hpA hpB hpC he).symm

include hsmall in
/-- Fourier coordinates of the genuine individual Hilbert noise are
exactly the native weighted Fourier tests of its literal scalar field. -/
theorem coefficients(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(k:ℕ)(ω:Ω)(l:ℤ):
    fourierCoeff (Value hL hρ k ω) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff
        (fun x:HeatCircle=>(Field k (ω,x):ℂ)) l:=by
  rw [value_eq_native 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ k ω]
  let A:=fun z:Ω×HeatCircle=>(Field k z:ℂ)
  have hA:Measurable A:=Complex.continuous_ofReal.measurable.comp
    (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k)
  exact NativeBesselFieldAE.coefficients Λ ρ hL hρ A hA ω
    ((MeasurableL2FieldAE.section_memLp_iff AddCircle.haarAddCircle A hA ω).mp
      (section_memLp 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF hFm hsmall (zero_le_one.trans hL) k ω).ofReal) l

local notation "Coord"=>MixedCanonicalWeightedPhysicalCoordinates.coordinate
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF hFm

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- A genuine original-J input for each Fourier test of this individual
noise, retaining the SAME input's full physical row identity. -/
theorem original_input_fourier(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)
    (a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff (Value hL hρ k ω) l)) ∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        ℓ (input z)=∫x:HeatCircle,
          NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l x*
          RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle:=by
  let w:ℝ:=(Λ+(l:ℝ)^2)^(-ρ/2)
  obtain ⟨input,hI,hr⟩:=MixedCanonicalWeightedPhysicalCoordinates.original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal (zero_le_one.trans hL) hbH hb1 hvb' w a l k
  refine ⟨input,hI.trans (ae_of_all _ (fun ω=>?_)),hr⟩
  change w*a (fourierCoeff (fun x:HeatCircle=>(Field k (ω,x):ℂ)) l)=
    a (fourierCoeff (Value hL hρ k ω) l)
  rw [coefficients 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall hL hρ k ω l]
  change w*a (fourierCoeff (fun x:HeatCircle=>(Field k (ω,x):ℂ)) l)=
    a (w • fourierCoeff (fun x:HeatCircle=>(Field k (ω,x):ℂ)) l)
  exact (map_smul a w _).symm

include hsmall hIJ₀ hIJ₁ hrootStop hrootTarget hcenter in
/-- One sample event identifies every real and imaginary Fourier output;
one energy event identifies all rows and all continuous linear tests. -/
theorem hilbert_noise_coefficients(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)(hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)(k:ℕ):
    ∃r i:ℤ→Process (E:=Both RealHaarInput) 𝓕 μ H,
      (∀ᵐω∂μ,∀l:ℤ,
        J.integral (r l) ω=(fourierCoeff (Value hL hρ k ω) l).re ∧
        J.integral (i l) ω=(fourierCoeff (Value hL hρ k ω) l).im) ∧
      ∀ᵐz∂energyMeasure μ H,∀l:ℤ,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        (ℓ (r l z)=∫x:HeatCircle,
          NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.reCLM l x*
          RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle) ∧
        (ℓ (i l z)=∫x:HeatCircle,
          NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.imCLM l x*
          RootSectionAverage.average R₀ k (Coord k ℓ) (z,x) ∂AddCircle.haarAddCircle):=by
  have hexR(l:ℤ):=original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hL hρ hbH hb1 hvb' Complex.reCLM l k
  have hexI(l:ℤ):=original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hL hρ hbH hb1 hvb' Complex.imCLM l k
  choose r hR using hexR
  choose i hI using hexI
  refine ⟨r,i,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr (fun l=>(hR l).1),
      ae_all_iff.mpr (fun l=>(hI l).1)] with ω hr hi l
    exact ⟨hr l,hi l⟩
  · filter_upwards [ae_all_iff.mpr (fun l=>(hR l).2),
      ae_all_iff.mpr (fun l=>(hI l).2)] with z hr hi l ℓ
    exact ⟨hr l ℓ,hi l ℓ⟩
end SHE.MixedCanonicalNoiseIncrement
