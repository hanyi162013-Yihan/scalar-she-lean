module
public import SHE.MixedOrdinaryNoiseHilbert
public import SHE.OrdinaryUncutSampleExpansion
public import SHE.ControlledReferenceFamilyEvaluation
public import SHE.MixedOrdinaryWeightedPhysicalCoordinates
public import SHE.NativeBesselFieldAE
public import SHE.PastParameterDiagonal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedOrdinaryRootFields
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedOrdinaryPhysicalCoordinates_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedOrdinaryPhysicalCoordinates_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedOrdinaryPhysicalCoordinates_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedOrdinaryNoiseHilbert_second:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance mixedOrdinaryPhysicalCoordinates_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedOrdinaryPhysicalCoordinates_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedOrdinaryPhysicalCoordinates_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedOrdinaryPhysicalCoordinates_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedOrdinaryPhysicalCoordinates_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedOrdinaryPhysicalCoordinates_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU"=>MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
variable (P:CanonicalCovariance.ProfileParameters)(hAs:BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable (Z:VariableObservations.Family HeatCircle 1)
variable (hstop:∀x,(Z.observations x 0).stop=(b:ℝ))(htarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,htarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hstop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:HeatCircle×WordRecursion.State 1=>F q.1 q.2))
local notation "Base"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm
local notation "R₀"=>referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb (0,0)
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Raw"=>(fun k p=>OrdinaryUncutPhysicalGradient.raw modelU (Base p) k)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "Noise"=>(fun k (z:Ω×History HeatCircle k)=>
  OrdinaryUncutNoise.value modelU (Base (pastParameter z.1)) k z.2 z.1)
local notation "NF"=>MixedOrdinaryWeightedPhysicalCoordinates.noiseField
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

local notation "U"=>(modelU).physicalState
local notation "X"=>(modelU).physicalField

def raw(i:Fin 2)(k:ℕ)(z:History HeatCircle k×Ω):ℝ:=
  if i=0 then ControlledReferenceFamilyEvaluation.leaf
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm U U X X (pastParameter z.2) k z.1 z.2
  else ControlledReferenceFamilyEvaluation.reference
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm U U X X (pastParameter z.2) k z.1 z.2
local notation "RawF"=>raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

def field(i:Fin 2)(k:ℕ):Ω×HeatCircle→ℝ:=
  RootSectionAverage.average R₀ k (fun z=>RawF i k (z.2,z.1))
local notation "Field"=>field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

include hsmall in
theorem raw_measurable(hΛ:0≤Λ)(i:Fin 2)(k:ℕ):Measurable (RawF i k):=by
  have hu:StronglyMeasurable pastParameter:=
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).mono (𝓕.le v)
  have hm:=ControlledReferenceFamilyEvaluation.diagonal_measurable
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm hsmall U U X X
    (modelU).physicalState_measurable (modelU).physicalState_measurable
    (modelU).physicalField_measurable (modelU).physicalField_measurable hΛ pastParameter hu k
  unfold raw
  by_cases hi:i=0
  · simpa only [hi,ite_true] using hm.1
  · simpa only [ite_eq_right hi] using hm.2

include hsmall in
theorem field_measurable(hΛ:0≤Λ)(i:Fin 2)(k:ℕ):Measurable (Field i k):=
  RootSectionAverage.measurable R₀ k _ ((raw_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ i k).comp measurable_swap)

theorem raw_bound(k:ℕ):∃C:ℝ,0≤C∧∀(i:Fin 2) h ω,
    ‖RawF i k (h,ω)‖≤C*UncutSmoothWords.weight (Base (0,0)) k h:=by
  obtain ⟨C,hC,hCb⟩:=ControlledReferenceFamilyEvaluation.evaluation_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm U U X X k
  refine ⟨C,hC,?_⟩
  intro i h ω
  unfold raw
  by_cases hi:i=0
  · simpa only [hi,ite_true] using (hCb (pastParameter ω) h ω).1
  · simpa only [ite_eq_right hi] using (hCb (pastParameter ω) h ω).2

include hsmall in
theorem field_bound(hΛ:0≤Λ)(k:ℕ):∃C:ℝ,0≤C∧∀(i:Fin 2) z,‖Field i k z‖≤C:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm k
  refine ⟨C*UncutHistoryMass.massBound (R:=R₀) (n:=1) (AddCircle.haarAddCircle:Measure HeatCircle) k,
    mul_nonneg hC (UncutHistoryMass.massBound_nonneg _ k),?_⟩
  intro i z
  exact RootSectionAverage.norm_le (Base (0,0)) k (fun a=>RawF i k (a.2,a.1))
    ((raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ i k).comp measurable_swap)
    C hC (fun ω h=>hCb i h ω) z.1 z.2

include hsmall in
theorem section_memLp(hΛ:0≤Λ)(i:Fin 2)(k:ℕ)(ω:Ω):
    MemLp (fun x:HeatCircle=>(Field i k (ω,x):ℂ)) 2 AddCircle.haarAddCircle:=by
  obtain ⟨C,hC,hCb⟩:=field_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ k
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp (field_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ i k)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
  apply ae_of_all
  intro x
  change ‖(Field i k (ω,x):ℂ)‖≤C
  simpa only [Complex.norm_real] using hCb i (ω,x)

include hsmall in
theorem field_integral(hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν]
    (i:Fin 2)(k:ℕ)(ω:Ω):
    (∫x,Field i k (ω,x) ∂ν)=∫h,RawF i k (h,ω) ∂historyMeasure R₀ ν k:=by
  obtain ⟨C,hC,hCb⟩:=raw_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm k
  have hm:=raw_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ i k
  have hi:Integrable (fun h=>RawF i k (h,ω)) (historyMeasure R₀ ν k):=
    ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).const_mul C).mono'
      (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun h=>hCb i h ω))
  exact (RootSectionAverage.integral_history R₀ ν k (fun z=>RawF i k (z.2,z.1)) ω hi).symm

include hsmall in
theorem leaf_mass(hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    (∫x,Field 0 k (ω,x) ∂ν)=
      OrdinaryUncutSampleExpansion.leafMass modelU (Base (pastParameter ω)) ν k ω:=by
  rw [field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ ν 0 k ω]
  unfold OrdinaryUncutSampleExpansion.leafMass
  rw [ControlledOrdinaryAverage.measure_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb ν (pastParameter ω) (0,0) k]
  apply integral_congr_ae
  filter_upwards with h
  change ControlledReferenceFamilyEvaluation.leaf P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z ht hs F hF hFm U U X X (pastParameter ω) k h ω=JointUncutWordEvaluation.leaf
      (Base (pastParameter ω)) 0 U U X X k h ω
  unfold ControlledReferenceFamilyEvaluation.leaf
  rw [OrdinaryJointSelf.uncutLeaf,OrdinaryJointSelf.uncutLeaf]

include hsmall in
theorem reference_mass(hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    (∫x,Field 1 k (ω,x) ∂ν)=
      OrdinaryUncutSampleExpansion.referenceMass modelU (Base (pastParameter ω)) ν k ω:=by
  rw [field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ ν 1 k ω]
  unfold OrdinaryUncutSampleExpansion.referenceMass
  rw [ControlledOrdinaryAverage.measure_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb ν (pastParameter ω) (0,0) k]
  apply integral_congr_ae
  filter_upwards with h
  change ControlledReferenceFamilyEvaluation.reference P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z ht hs F hF hFm U U X X (pastParameter ω) k h ω=JointUncutWordEvaluation.reference
      (Base (pastParameter ω)) 0 U U X X k h ω
  unfold ControlledReferenceFamilyEvaluation.reference JointUncutWordEvaluation.reference
  rw [OrdinaryJointSelf.state,OrdinaryJointSelf.state]

/-- Original scalar-history L1 for the genuine ordinary kth noise. -/
theorem noise_integrable(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>Noise k (ω,h)) (historyMeasure R₀ ν k):=by
  obtain ⟨C,hC,hCb⟩:=ControlledOrdinaryNoise.value_bound
    P (fun z=>κ+aV z) hAs Λ θ v b hvb Z ht hs F hF hFm modelU k
  have hm:Measurable (fun h:History HeatCircle k=>Noise k (ω,h)):=
    (OrdinaryUncutNoise.value_measurable modelU (Base (pastParameter ω)) k).comp
      (measurable_id.prodMk measurable_const)
  exact ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).const_mul C).mono'
    hm.aestronglyMeasurable (ae_of_all _ (fun h=>hCb (pastParameter ω) h ω))

theorem noise_mass(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    (∫x,NF k (ω,x) ∂ν)=
      OrdinaryUncutSampleExpansion.noiseMass modelU (Base (pastParameter ω)) ν k ω:=by
  change (∫x,RootSectionAverage.average R₀ k (Noise k) (ω,x) ∂ν)=_
  rw [←RootSectionAverage.integral_history R₀ ν k (Noise k) ω
    (noise_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
      P hAs θ v b hvb Z hstop htarget F hF hFm ν k ω)]
  unfold OrdinaryUncutSampleExpansion.noiseMass
  rw [ControlledOrdinaryAverage.measure_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb ν (pastParameter ω) (0,0) k]

def error(k:ℕ)(z:Ω×HeatCircle):ℝ:=Field 0 k z-Field 1 k z-NF k z-Field 0 (k+1) z
local notation "Error"=>error
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs θ v b hvb Z hstop htarget F hF hFm

include hsmall in
/-- The explicit discrepancy in the ordinary recursion is the actual
rough-minus-smooth bracket insertion with its POSITIVE sign. -/
theorem error_eq_mass(hΛ:0≤Λ)(k:ℕ)(ω:Ω)(x:HeatCircle):
    Error k (ω,x)=
      OrdinaryUncutSampleExpansion.errorMass modelU (Base (pastParameter ω)) (Measure.dirac x) k ω:=by
  have hL:=leaf_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ (Measure.dirac x) k ω
  have hR:=reference_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ (Measure.dirac x) k ω
  have hN:=noise_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm (Measure.dirac x) k ω
  have hNext:=leaf_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs θ v b hvb Z hstop htarget F hF hFm hsmall hΛ (Measure.dirac x) (k+1) ω
  simp only [integral_dirac] at hL hR hN hNext
  have hcycle:=OrdinaryUncutSampleExpansion.sample_cycle modelU (Base (pastParameter ω)) (Measure.dirac x) k ω
  change Field 0 k (ω,x)-Field 1 k (ω,x)-NF k (ω,x)-Field 0 (k+1) (ω,x)=_
  linarith only [hL,hR,hN,hNext,hcycle]
end SHE.MixedOrdinaryRootFields
