module
public import SHE.JointGammaFirstPairRecursion
public import SHE.RootSectionZero
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
namespace SHE.JointGammaRootRecursion
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
local notation "ht"=>(fun (x:HeatCircle) (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootTarget] using (le_refl (b:ℝ)))
local notation "hs"=>(fun (x:HeatCircle) (i:Fin 1)=>by simpa only [Subsingleton.elim i 0,hrootStop] using (le_refl (b:ℝ)))
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "R₀"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "R1"=>referenceData P (fun z=>κ+aV z) hAs Λ 1 v b hvb (0,0)
local notation "R0"=>referenceData P (fun z=>κ+aV z) hAs Λ 0 v b hvb (0,0)
local notation "Base1"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 1 v b hvb Z ht hs F hF hFm
local notation "Base0"=>ControlledReferenceFamilyLevel.level P (fun z=>κ+aV z) hAs Λ 0 v b hvb Z ht hs F hF hFm
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

variable (hΛ:0≤Λ)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
local notation "DU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
local notation "DV"=>MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
include hrootTarget in
theorem fixedTarget (x:HeatCircle)(i:Fin 1):(b:ℝ)≤(Z.observations x i).target:=by
  simpa only [Subsingleton.elim i 0,hrootTarget] using (le_refl (b:ℝ))
include hrootStop in
theorem fixedStop (x:HeatCircle)(i:Fin 1):(b:ℝ)≤(Z.observations x i).stop:=by
  simpa only [Subsingleton.elim i 0,hrootStop] using (le_refl (b:ℝ))
local notation "Fixed" θ:max p:max x:max=>ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb
  (Z.observations x) (fixedTarget b Z hrootTarget x) (fixedStop b Z hrootStop x) (F x) (hF.boundedSmooth x) p
local notation "JF"=>MixedCanonicalRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OF"=>MixedOrdinaryRootFields.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm
local notation "OE"=>MixedOrdinaryRootFields.error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm

include hsmall hΛ in
/-- Fixing the retained root before the first joint insertion gives
exactly the actual root-retained next joint leaf field. -/
theorem joint_next(ω:Ω)(x:HeatCircle):
    MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ u₀ S (Fixed 1 (pastParameter ω) x) () ω=JF 0 1 (ω,x):=by
  have hn:=JointUncutSuccessor.averaged_eq (Base1 (pastParameter ω)) Λ
    (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField
    (DU).physicalState_measurable (DV).physicalState_measurable
    (DU).physicalField_measurable (DV).physicalField_measurable (Measure.dirac x) 0 ω
  change (∫p:HeatCircle,JointUncutLocalRemainder.value (Base1 (pastParameter ω)) Λ
      (DU).physicalState (DV).physicalState (DU).physicalField (DV).physicalField 0 p ω ∂Measure.dirac x)=_ at hn
  rw [integral_dirac] at hn
  have hf:=MixedCanonicalRootFields.field_integral 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm hsmall hΛ (Measure.dirac x) 0 1 ω
  rw [integral_dirac] at hf
  have hm:=ControlledOrdinaryAverage.measure_eq P (fun z=>κ+aV z) hAs Λ 1 v b hvb
    (Measure.dirac x) (pastParameter ω) (0,0) 1
  rw [hm] at hn
  rw [hf]
  simp only [JointUncutLocalRemainder.value,UncutSmoothWords.weight,one_mul] at hn
  convert! hn using 1 <;> rfl

include hsmall hΛ in
/-- The companion insertion along genuine ordinary U gives its actual
root-retained next leaf field, with no joint-theta-zero process. -/
theorem ordinary_next(ω:Ω)(x:HeatCircle):
    ActualUncutRemainder.value (Fixed 0 (pastParameter ω) x) (fun z=>κ+aV z)
      (DU).physicalState (DU).physicalField 0 () ω=OF 0 1 (ω,x):=by
  have hn:=JointUncutSuccessor.averaged_eq (Base0 (pastParameter ω)) 0
    (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField
    (DU).physicalState_measurable (DU).physicalState_measurable
    (DU).physicalField_measurable (DU).physicalField_measurable (Measure.dirac x) 0 ω
  change (∫p:HeatCircle,JointUncutLocalRemainder.value (Base0 (pastParameter ω)) 0
      (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField 0 p ω ∂Measure.dirac x)=_ at hn
  rw [integral_dirac,OrdinaryJointSelf.uncutLocalRemainder] at hn
  have hf:=MixedOrdinaryRootFields.leaf_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget
    F hF hFm hsmall hΛ (Measure.dirac x) 1 ω
  rw [integral_dirac] at hf
  rw [hf]
  convert! hn using 1 <;> rfl

/-- Depth-zero full joint mark retains exactly its physical root. -/
theorem joint_mark(ω:Ω)(x:HeatCircle):
    MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ u₀ S (Fixed 1 (pastParameter ω) x) 0 () ω=JF 2 0 (ω,x):=by
  unfold MixedCanonicalRootFields.field
  rw [RootSectionZero.average]
  rfl

include hsmall hΛ in
/-- The independently ordinary depth-zero discrepancy is precisely
actual rough-minus-companion insertion, with its positive error sign. -/
theorem ordinary_error(ω:Ω)(x:HeatCircle):
    ActualUncutRemainder.value (Fixed 0 (pastParameter ω) x) (fun z=>κ+aU z)
      (DU).physicalState (DU).physicalField 0 () ω-
    ActualUncutRemainder.value (Fixed 0 (pastParameter ω) x) (fun z=>κ+aV z)
      (DU).physicalState (DU).physicalField 0 () ω=OE 0 (ω,x):=by
  have he:=MixedOrdinaryRootFields.error_eq_mass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs 0 v b hvb Z hrootStop hrootTarget
    F hF hFm hsmall hΛ 0 ω x
  unfold OrdinaryUncutSampleExpansion.errorMass at he
  change OE 0 (ω,x)=(∫p:HeatCircle,_ ∂Measure.dirac x) at he
  rw [integral_dirac] at he
  convert! he.symm using 1 <;> rfl
variable (hκP:κ<P.lower)(hbH:b≤H)(hH:(H:ℝ)≤1)
variable (B:ℝ≥0)(hBDG:StandardTerminalBDG16 J B)
local notation "Ret" x:max θ:max ω:max=>JointGammaRetainedRecursion.retained (F:=F x)
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (Z.observations x) J P hκP hΛ v b
  (fixedTarget b Z hrootTarget x) hbH hvb θ ω
include hsmall B hBDG hH in
/-- The true retained first-pair drift is the exact already constructed
root-retained error/mark and next ordinary/joint leaf fields. -/
theorem retained_pair(hb0:0<b)(x:HeatCircle):∀ᵐω∂μ,
    Ret x 0 ω-Ret x 1 ω=OE 0 (ω,x)+OF 0 1 (ω,x)-(JF 2 0 (ω,x)+JF 0 1 (ω,x)):=by
  have hst:∀i,(Z.observations x i).stop=(Z.observations x i).target:=by
    intro i
    simp only [Subsingleton.elim i 0,hrootStop,hrootTarget]
  have h0:=JointGammaOrdinaryRetained.zero_eq_actual_remainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S (Z.observations x) J P hκP hΛ v b (fixedTarget b Z hrootTarget x) hbH hvb
    hst (hF.boundedSmooth x) hAs hH B hBDG hIJ₀ hIJ₁ hb0
  have h1:=JointGammaRetainedRecursion.one_eq_mark_remainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ u₀ S (Z.observations x) J P hκP hΛ v b (fixedTarget b Z hrootTarget x) hbH hvb
    hst (hF.boundedSmooth x) hAs hH B hBDG hIJ₀ hIJ₁ hb0
  filter_upwards [h0,h1] with ω h0 h1
  have hj:=joint_next 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs
    v b hvb Z hrootStop hrootTarget F hF hFm hΛ hsmall ω x
  have ho:=ordinary_next 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs
    v b hvb Z hrootStop hrootTarget F hF hFm hΛ hsmall ω x
  have hm:=joint_mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs
    v b hvb Z hrootStop hrootTarget F hF hFm ω x
  have he:=ordinary_error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs
    v b hvb Z hrootStop hrootTarget F hF hFm hΛ hsmall ω x
  have h0fixed:Ret x 0 ω=ActualUncutRemainder.value (Fixed 0 (pastParameter ω) x)
      (fun z=>κ+aU z) (DU).physicalState (DU).physicalField 0 () ω:=by
    convert! h0 using 1
  have h1fixed:Ret x 1 ω=
      MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ u₀ S (Fixed 1 (pastParameter ω) x) () ω+
      MixedJointUncutMark.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
        I₀ I₁ u₀ u₀ S (Fixed 1 (pastParameter ω) x) 0 () ω:=by
    convert! h1 using 1
  linear_combination h0fixed-h1fixed+he+ho-hj-hm

end SHE.JointGammaRootRecursion
