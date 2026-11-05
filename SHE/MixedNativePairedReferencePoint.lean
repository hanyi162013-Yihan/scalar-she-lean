module
public import SHE.MixedNativeTreeEndpoints
public import SHE.MixedNativeTreeAverages
public import SHE.MixedPastNewestOrdinaryState
public import SHE.MixedNativeRootTransfer
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
namespace SHE.MixedNativePairedReferencePoint
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality CutoffCarriers
open scoped NNReal ENNReal
local instance mixedNativePairedReferencePoint_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativePairedReferencePoint_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativePairedReferencePoint_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativePairedReferencePoint_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativePairedReferencePoint_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativePairedReferencePoint_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativePairedReferencePoint_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativePairedReferencePoint_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativePairedReferencePoint_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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

local notation "BP"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z ht hs F hF hFm
local notation "Zero"=>BP (0,(0,0))
local notation "Endpoint"=>MixedNativeMarkedBudgets.endpoint
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z ht hs F hF hFm

theorem raw_endpoints(hA:P.coefficient=(fun z=>κ+aV z))
    (k:ℕ)(h:History HeatCircle k)(ω:Ω)
    (hactive:(v:ℝ)<(carrier Zero k).terminal h):
    JR 1 k (h,ω)=Endpoint k 1 v ω h ∧ OR 1 k (h,ω)=Endpoint k 0 v ω h:=by
  have hσ:∀x i,(Z.observations x i).stop=(b:ℝ):=by
    intro x i
    simpa only [Subsingleton.elim i 0] using hrootStop x
  have hT:∀x i,(Z.observations x i).target=(b:ℝ):=by
    intro x i
    simpa only [Subsingleton.elim i 0] using hrootTarget x
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hσ x i,hT x i]
  have hroot:∀x i,(Z.observations x i).stop≤(b:ℝ):=fun x i=>(hσ x i).le
  have hj:=MixedNativeTreeEndpoints.endpoint_one_eq_joint_reference
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z ht hs F hF hFm hages hroot k h ω hactive
  have hm:=MixedPastBaselineFTCIdentity.mean_eq_meanField
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P haP v b hvb Z ht hs F hF hFm hages hroot k h 0 v hactive ω
  have ho:=MixedPastNewestOrdinaryState.mean_zero_eq_observe
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z ht hs F hF hFm hages hroot k h v hactive ω
  have hstate:
      WordRecursion.observe (fun t=>(DU).physicalState (ω,t)) (fun p=>(DU).physicalField (ω,p))
        ((carrier Zero k).observations.observations h) v=
      JointWordAnalytic.state (carrier (BP (0,pastParameter ω)) k) Λ
        (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField h ω v:=by
    unfold JointWordAnalytic.state
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient haP Λ v b hvb Z ht hs F hF hFm (0,pastParameter ω) (0,(0,0)) k h]
    apply PiLp.ext
    intro i
    simp only [JointWordObserve.evaluate,WithLp.ofLp_toLp,sub_self,mul_zero,add_zero]
  have he0:Endpoint k 0 v ω h=
      JointUncutWordEvaluation.reference (BP (0,pastParameter ω)) Λ
        (DU).physicalState (DU).physicalState (DU).physicalField (DU).physicalField k h ω:=by
    unfold MixedNativeMarkedBudgets.endpoint ControlledFamilyFrontFields.activeValue
    change (if (v:ℝ)≤v ∧ (v:ℝ)<(carrier (BP (0,pastParameter ω)) k).terminal h
      then _ else 0)=_
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ v b hvb Z ht hs F hF hFm
      (0,pastParameter ω) (0,(0,0)) k h,ite_eq_left ⟨le_rfl,hactive⟩,
      ControlledFamilyReferenceAtPast.value_at_past_eq_node_average
        P P.coefficient haP Λ v b hvb Z ht hs F hF hFm]
    unfold JointUncutWordEvaluation.reference
    rw [hm,ho,hstate]
    rfl
  simp only [MixedCanonicalRootFields.raw,MixedOrdinaryRootFields.raw,
    ControlledReferenceFamilyEvaluation.reference,show ¬((1:Fin 2)=0) from by decide,ite_false]
  generalize hC:(fun z=>κ+aV z)=C at hAs ⊢
  have hPC:C=P.coefficient:=hC.symm.trans hA.symm
  clear hC
  subst C
  constructor
  · convert! hj.symm using 1 <;> rfl
  · convert! he0.symm using 1 <;> rfl

end SHE.MixedNativePairedReferencePoint

