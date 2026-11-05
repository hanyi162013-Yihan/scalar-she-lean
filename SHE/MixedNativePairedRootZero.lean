module
public import SHE.RootSectionZero
public import SHE.ScalarRootHeatLeaf
public import SHE.MixedNativePairedLeafHilbert
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
namespace SHE.MixedNativePairedRootZero
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


local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "JR"=>MixedCanonicalRootFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OR"=>MixedOrdinaryRootFields.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "WordDiff"=>MixedPastTerminalEndpointWord.wordDifference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z ht hs F hF hFm

include hrootStop hrootTarget hcenter in
/-- The zeroth paired leaf is the literal terminal scalar difference,
independent of the chosen moving past or its window length. -/
theorem raw_zero (ω:Ω)(x:HeatCircle):
    JR 0 0 (x,ω)-OR 0 0 (x,ω)=
      F x (ScalarRootHeatLeaf.scalarState ((DV).physicalField (ω,((b:ℝ),x))))-
      F x (ScalarRootHeatLeaf.scalarState ((DU).physicalField (ω,((b:ℝ),x)))):=by
  have hj:=ScalarRootHeatLeaf.literal_leaf_eq
    (Base1 (pastParameter ω)) (b:ℝ) (fun _=>rfl) hrootStop hrootTarget hcenter DU DV Λ x ω
  have ho:=ScalarRootHeatLeaf.literal_leaf_eq
    (Base0 (pastParameter ω)) (b:ℝ) (fun _=>rfl) hrootStop hrootTarget hcenter DU DU Λ x ω
  change JointWordAnalytic.leaf (Base1 (pastParameter ω)) Λ
      (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField x ω-
    JointWordAnalytic.leaf (Base0 (pastParameter ω)) Λ
      (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField x ω=_
  exact congrArg₂ (fun y z:ℝ=>y-z) hj ho

/-- Literal terminal scalar difference on the original native circle. -/
def field(z:Ω×HeatCircle):ℝ:=
  F z.2 (ScalarRootHeatLeaf.scalarState ((DV).physicalField (z.1,((b:ℝ),z.2))))-
  F z.2 (ScalarRootHeatLeaf.scalarState ((DU).physicalField (z.1,((b:ℝ),z.2))))
local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S b F

include hFm in
theorem field_measurable:Measurable Field:=by
  have hv:Measurable (fun z:Ω×HeatCircle=>(DV).physicalField (z.1,((b:ℝ),z.2))):=
    (DV).physicalField_measurable.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hu:Measurable (fun z:Ω×HeatCircle=>(DU).physicalField (z.1,((b:ℝ),z.2))):=
    (DU).physicalField_measurable.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact (hFm.comp (measurable_snd.prodMk (ScalarRootHeatLeaf.scalarState_continuous.measurable.comp hv))).sub
    (hFm.comp (measurable_snd.prodMk (ScalarRootHeatLeaf.scalarState_continuous.measurable.comp hu)))

local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OF"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm

include hrootStop hrootTarget hcenter in
theorem field_difference(ω:Ω)(x:HeatCircle):JF 0 0 (ω,x)-OF 0 0 (ω,x)=Field (ω,x):=by
  change RootSectionAverage.average R1 0 (fun z:Ω×HeatCircle=>JR 0 0 (z.2,z.1)) (ω,x)-
    RootSectionAverage.average R0 0 (fun z:Ω×HeatCircle=>OR 0 0 (z.2,z.1)) (ω,x)=_
  rw [RootSectionZero.average,RootSectionZero.average]
  exact raw_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget hcenter F hF hFm ω x

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
include hsmall haP hcenter in
/-- The native left side of every finite paired expansion is exactly the
terminal scalar difference. Each frequency may choose its own window. -/
theorem leaf_eq_native(hA:P.coefficient=(fun z=>κ+aV z))(ω:Ω):
    MixedNativePairedHilbertExpansion.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ 0 ω=
    NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field z:ℂ)) ω:=by
  symm
  apply MixedNativePairedLeafHilbert.native_eq_of_section
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hL hρ hA
    Field (field_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S b F hFm) 0 ω
  apply ae_of_all
  intro x
  rw [MixedNativePairedLeafAverage.field_difference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hsmall hA (zero_le_one.trans hL)]
  exact (field_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ hnull hJ P hAs v b hvb Z hrootStop hrootTarget hcenter F hF hFm ω x).symm

include hsmall haP hcenter in
/-- The actual terminal native scalar difference equals the finite
reference/noise/full-mark sum and the literal high-order leaf. -/
theorem finite_expansion(hA:P.coefficient=(fun z=>κ+aV z))(depth:ℕ)(ω:Ω):
    NativeBesselFieldAE.value Λ ρ hL hρ (fun z:Ω×HeatCircle=>(Field z:ℂ)) ω=
      (∑k∈Finset.range depth,MixedNativePairedHilbertExpansion.reference
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ k ω)+
      (∑k∈Finset.range depth,MixedNativeHigherOriginalEnergy.value
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ k ω)+
      (∑k∈Finset.range depth,MixedNativePairedHilbertExpansion.mark
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ k ω)+
      MixedNativePairedHilbertExpansion.leaf
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ depth ω:=by
  rw [←leaf_eq_native 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P haP hAs v b hvb Z hrootStop hrootTarget hcenter F hF hFm hsmall hL hρ hA ω]
  exact MixedNativePairedHilbertExpansion.finite_expansion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs v b hvb Z hrootStop hrootTarget F hF hFm hL hρ hsmall depth ω
end SHE.MixedNativePairedRootZero
