module
public import SHE.MixedNativePairedReferencePoint
public import SHE.RootSectionRelativeIdentity
public import SHE.HistoryPastWindow
public import SHE.NativeBesselDifferenceIdentity
public import SHE.ControlledPairedUncutLeafIdentity
public import SHE.MixedPastTerminalEndpointWord
public import SHE.RootSectionLinear
public import SHE.MixedOrdinaryRootHilbertExpansion
public import SHE.MixedCanonicalRootHilbertExpansion
public import SHE.MixedNativeHigherOriginalEnergy
public import SHE.MixedNativePairedOriginalInput
public import SHE.MixedNativeOriginalFourierRows
public import SHE.MixedPastNativeCompleteSections
public import SHE.NativeOriginalRowsEnergy
public import SHE.MixedCanonicalNoiseIncrement
public import SHE.MixedOrdinaryNoiseHilbert
public import SHE.MixedOrdinaryCoordinateMass
public import SHE.MixedNativeColumnRawFourier
public import SHE.RootSectionLinear
public import SHE.NativeMultiplierFourierIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option quotPrecheck false
namespace SHE.MixedNativePairedReferenceAverage
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativePairedOriginalInput_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativePairedOriginalInput_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativePairedOriginalInput_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativePairedOriginalInput_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativePairedOriginalInput_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativePairedOriginalInput_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativePairedOriginalInput_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
local notation "modelU"=>MixedNativeOrdinaryModel.model 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (hAs:BoundedSmooth (fun z=>κ+aV z))
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (hrootStop:∀x,(Z.observations x 0).stop=(b:ℝ))
variable (hrootTarget:∀x,(Z.observations x 0).target=(b:ℝ))
variable (hcenter:∀x,(Z.observations x 0).center=x)
local notation "ht"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootTarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun x (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootStop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "R1"=>referenceData P (fun z=>κ+aV z) hAs Λ 1 v b hvb (0,0)
local notation "R0"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)
local notation "Base1"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 1 v b hvb Z ht hs F hF hFm
local notation "Base0"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 0 v b hvb Z ht hs F hF hFm
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v



local notation "JR"=>MixedCanonicalRootFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OR"=>MixedOrdinaryRootFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OF"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "WordDiff"=>MixedPastTerminalEndpointWord.wordDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z ht hs F hF hFm

local notation "BP"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z ht hs F hF hFm
local notation "Zero"=>BP (0,(0,0))
local notation "Endpoint"=>MixedNativeMarkedBudgets.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z ht hs F hF hFm

def field(k:ℕ)(z:Ω×HeatCircle):ℝ:=
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z ht hs F hF hFm k 1 v z-
  MixedNativeRootTransfer.averagedEndpoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z ht hs F hF hFm k 0 v z
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z hrootStop hrootTarget F hF hFm
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
theorem joint_integrable(hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>JR 1 k (h,ω)) (historyMeasure R0 ν k):=by
  obtain ⟨C,hC,hCb⟩:=MixedCanonicalRootFields.raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hΛ k
  have hm:=MixedCanonicalRootFields.raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hΛ 1 k
  have hi:Integrable (fun h=>JR 1 k (h,ω)) (historyMeasure R1 ν k):=
    ((UncutHistoryMass.weight_integrable (Base1 (0,0)) ν k).const_mul C).mono'
      (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (ae_of_all _ (fun h=>hCb 1 h ω))
  have hmeasure:historyMeasure R1 ν k=historyMeasure R0 ν k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=R1) (Q:=R0) rfl rfl ν k
  exact hmeasure ▸ hi

include hsmall in
theorem ordinary_integrable(hΛ:0≤Λ)(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>OR 1 k (h,ω)) (historyMeasure R0 ν k):=by
  obtain ⟨C,hC,hCb⟩:=MixedOrdinaryRootFields.raw_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm k
  have hm:=MixedOrdinaryRootFields.raw_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ 1 k
  exact ((UncutHistoryMass.weight_integrable (Base0 (0,0)) ν k).const_mul C).mono'
    (hm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (ae_of_all _ (fun h=>hCb 1 h ω))

include hsmall in
/-- The two retained-root finite-expansion references are exactly the
two past-time endpoints of the actual three-leg comparison. Original
history integrability is proved at each retained root before averaging. -/
theorem field_difference(hA:P.coefficient=(fun z=>κ+aV z))(hΛ:0≤Λ)(hvb':v<b)
    (k:ℕ)(ω:Ω)(x:HeatCircle):
    Field k (ω,x)=JF 1 k (ω,x)-OF 1 k (ω,x):=by
  let ν:Measure HeatCircle:=Measure.dirac x
  have hm0:historyMeasure R0 ν k=historyMeasure R₀ ν k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=R0) (Q:=R₀) rfl rfl ν k
  have hj:=joint_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ ν k ω
  have ho:=ordinary_integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ ν k ω
  rw [hm0] at hj ho
  have hroot:∀x,(v:ℝ)<(Zero).terminal x:=fun _=>by exact_mod_cast hvb'
  have he:∀ᵐh∂historyMeasure R₀ ν k,
      JR 1 k (h,ω)=Endpoint k 1 v ω h ∧ OR 1 k (h,ω)=Endpoint k 0 v ω h:=by
    filter_upwards [HistoryPastWindow.carrier_after_past_ae Zero hroot ν k] with h hh
    exact MixedNativePairedReferencePoint.raw_endpoints 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hA k h ω hh
  have hi1:=hj.congr (he.mono (fun h hh=>hh.1))
  have hi0:=ho.congr (he.mono (fun h hh=>hh.2))
  have h1:=RootSectionAverage.integral_dirac_history R₀ k x (fun h=>Endpoint k 1 v ω h) hi1
  have h0:=RootSectionAverage.integral_dirac_history R₀ k x (fun h=>Endpoint k 0 v ω h) hi0
  have hJF:=MixedCanonicalRootFields.field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hΛ ν 1 k ω
  have hOF:=MixedOrdinaryRootFields.field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ ν 1 k ω
  have hm1:historyMeasure R1 ν k=historyMeasure R₀ ν k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=R1) (Q:=R₀) rfl rfl ν k
  rw [hm1] at hJF
  rw [hm0] at hOF
  simp only [ν,integral_dirac] at hJF hOF
  unfold field MixedNativeRootTransfer.averagedEndpoint
  rw [RootSectionRelativeIdentity.eq,RootSectionRelativeIdentity.eq]
  change RootSectionAverage.average R₀ k (fun a=>Endpoint k 1 v a.1 a.2) (ω,x)-
    RootSectionAverage.average R₀ k (fun a=>Endpoint k 0 v a.1 a.2) (ω,x)=_
  change (∫h,Endpoint k 1 v ω h ∂historyMeasure R₀ (Measure.dirac x) k)=
    RootSectionAverage.average R₀ k (fun a=>Endpoint k 1 v a.1 a.2) (ω,x) at h1
  change (∫h,Endpoint k 0 v ω h ∂historyMeasure R₀ (Measure.dirac x) k)=
    RootSectionAverage.average R₀ k (fun a=>Endpoint k 0 v a.1 a.2) (ω,x) at h0
  rw [←h1,←h0]
  rw [integral_congr_ae (he.mono (fun h hh=>hh.1.symm)),
    integral_congr_ae (he.mono (fun h hh=>hh.2.symm)),←hJF,←hOF]

end SHE.MixedNativePairedReferenceAverage

