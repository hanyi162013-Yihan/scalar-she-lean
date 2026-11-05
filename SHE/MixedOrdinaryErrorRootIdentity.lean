module
public import SHE.MixedOrdinaryErrorPrimitive
public import SHE.MixedOrdinaryFirstHit
public import SHE.MixedOrdinaryRootFields
public import SHE.ControlledActualTimeRemainder
public import SHE.MixedPastNewestUncutError
public import SHE.MixedPastNewestOriginalMass
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
namespace SHE.MixedOrdinaryErrorRootIdentity
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




local notation "Error"=>MixedOrdinaryRootFields.error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "Primitive"=>MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "Ages"=>MixedOrdinaryErrorPrimitive.ages b Z hrootStop hrootTarget
local notation "Upper"=>MixedOrdinaryErrorPrimitive.stopUpper b Z hrootStop
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hsmall in
/-- The actual positive ordinary discrepancy in the finite expansion
is exactly the repaired original-history primitive, at every retained
root. History L1 is established before the Dirac-root disintegration. -/
theorem error_eq_average(hP:P.coefficient=(fun z=>κ+aV z))(hΛ:0≤Λ)(k:ℕ)(ω:Ω)(x:HeatCircle):
    Error k (ω,x)=RootSectionAverage.average Rzero k (Primitive k) (ω,x):=by
  have hroot:=MixedOrdinaryRootFields.error_eq_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hsmall hΛ k ω x
  have hfirst:=MixedOrdinaryFirstHit.error_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP v b hvb Z ht hs F hF hFm hP Ages Upper (Measure.dirac x) k ω
  have hmass:Error k (ω,x)=
      ∫h,Primitive k (ω,h) ∂historyMeasure Rzero (Measure.dirac x) k:=by
    apply hroot.trans
    clear hroot
    generalize hC:(fun z=>κ+aV z)=C at hAs ⊢
    have hPC:C=P.coefficient:=hC.symm.trans hP.symm
    clear hC
    subst C
    convert! hfirst using 1 <;> rfl
  exact hmass.trans (RootSectionAverage.integral_dirac_history Rzero k x (fun h=>Primitive k (ω,h))
    (MixedOrdinaryErrorPrimitive.integrable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z hrootStop hrootTarget F hF hFm (Measure.dirac x) k ω))

include hsmall in
/-- Actual ordinary finite-expansion errors, with their original signs
and weights, equal the SAME canonical finite coefficient-error field
whose uniform bound and approximation limit were already proved. -/
theorem canonical_finite_field_eq_ae(hP:P.coefficient=(fun z=>κ+aV z))(hΛ:0≤Λ)
    (D:SmoothApproximation.ScalarData)(j:ℕ)
    (hU:aU=D.residualCoefficient)(hV:aV=D.smoothCoefficient j)(depth:ℕ)(w:ℕ→ℝ):
    ∀ᵐz:Ω×HeatCircle∂μ.prod AddCircle.haarAddCircle,
      (∑k∈Finset.range depth,w k*Error k z)=
        MixedPastNewestFiniteError.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm D j depth w (z.2,z.1):=by
  filter_upwards [MixedPastNewestOrdinaryError.canonical_finite_field_eq_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
    D j hU hV Ages depth w] with z hz
  have he(k:ℕ):Error k z=RootSectionAverage.average Rzero k (Primitive k) z:=
    error_eq_average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hP hΛ k z.1 z.2
  simp_rw [he]
  exact hz
end SHE.MixedOrdinaryErrorRootIdentity
