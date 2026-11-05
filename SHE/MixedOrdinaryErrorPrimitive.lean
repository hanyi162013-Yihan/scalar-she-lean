module
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
namespace SHE.MixedOrdinaryErrorPrimitive
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
local notation "Base"=>ControlledReferenceFamilyLevel.level P P.coefficient haP Λ 0 v b hvb Z ht hs F hF hFm
local notation "Rzero"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "Primitive"=>MixedPastNewestOrdinaryError.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm
local notation "Difference"=>MixedPastNewestUncutError.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm

def ages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
  intro x i
  simpa only [Subsingleton.elim i 0,hrootStop,hrootTarget] using (le_refl (b:ℝ))

def stopUpper:∀x i,(Z.observations x i).stop≤(b:ℝ):=by
  intro x i
  simpa only [Subsingleton.elim i 0,hrootStop] using (le_refl (b:ℝ))
local notation "Ages"=>ages b Z hrootStop hrootTarget
local notation "Upper"=>stopUpper b Z hrootStop

/-- Literal original error primitives have a fixed-smooth-depth coarse
history majorant. This is only for applicability; it is not the uniform
approximation estimate used later in the proof. -/
theorem bound(k:ℕ):∃C:ℝ,0≤C∧∀z:Ω×History HeatCircle k,
    ‖Primitive k z‖≤C*UncutSmoothWords.weight (Base (0,0)) k z.2:=by
  have hM:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hcapU(z):|κ+aU z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbU z).1))]
    exact add_le_add le_rfl (hbU z).2
  have hcapV(z):|κ+aV z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg hκ.le (hell.le.trans (hbV z).1))]
    exact add_le_add le_rfl (hbV z).2
  obtain ⟨C,hC,hCb⟩:=ControlledActualTimeRemainder.remainder_bound P P.coefficient haP Λ 0 v b hvb Z ht hs F hF hFm
    (fun z=>κ+aU z) (add_nonneg hκ.le hM) hcapU (DU).physicalState (DU).physicalField k
  obtain ⟨D,hD,hDb⟩:=ControlledActualTimeRemainder.remainder_bound P P.coefficient haP Λ 0 v b hvb Z ht hs F hF hFm
    (fun z=>κ+aV z) (add_nonneg hκ.le hM) hcapV (DU).physicalState (DU).physicalField k
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro z
  rw [MixedPastNewestUncutError.primitive_eq_difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm Ages Upper]
  have hR(a:ℝ→ℝ)(K:ℝ)
      (hb:∀p:Inputs,∀h ω,‖PhysicalIto.wordRemainder
        ((UncutWordEvaluation.normalizedLevel (Base p) k).window h) a
        (fun t=>(DU).physicalState (ω,t)) (fun q=>(DU).physicalField (ω,q))
        ((UncutWordEvaluation.normalizedLevel (Base p) k).test h)‖≤K):
      ‖ActualUncutRemainder.value (Base (pastParameter z.1)) a (DU).physicalState (DU).physicalField k z.2 z.1‖≤
        K*UncutSmoothWords.weight (Base (0,0)) k z.2:=by
    rw [ActualUncutRemainder.value,norm_mul,Real.norm_eq_abs,
      abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base (pastParameter z.1)) k z.2)]
    rw [ControlledReferenceFamilyBounds.weight_eq P P.coefficient haP Λ 0 v b hvb Z ht hs F hF hFm (pastParameter z.1) (0,0) k z.2]
    exact (mul_le_mul_of_nonneg_left (hb _ _ _) (UncutSmoothWords.weight_nonneg (Base (0,0)) k z.2)).trans_eq
      (mul_comm _ _)
  exact (norm_sub_le _ _).trans ((add_le_add (hR _ C hCb) (hR _ D hDb)).trans_eq (by ring))

theorem measurable(k:ℕ):Measurable (Primitive k):=by
  let e:=MixedPastNewestOrdinaryError.errorField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hu:Measurable (Function.uncurry S.first):=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hn:=PredictableScalarField.nativeField_measurable hu
  have he:Measurable e:=(haU.comp hn).sub (haV.comp hn)
  have hc:=MixedPastNewestOriginalMass.current_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm k e he
  have hp:Measurable (MixedPastNewestOriginalMass.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm k e):=
    hc.stronglyMeasurable.integral_prod_left' |>.measurable
  have hid:Primitive k=MixedPastNewestOriginalMass.primitive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm k e:=
    funext (MixedPastNewestOrdinaryError.primitive_eq_error 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z ht hs F hF hFm Ages k)
  rw [hid]
  exact hp

/-- Original-history L1 is proved at every finite root measure, including
each Dirac root, before any retained-root/error identification. -/
theorem integrable(ν:Measure HeatCircle)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    Integrable (fun h=>Primitive k (ω,h)) (historyMeasure Rzero ν k):=by
  obtain ⟨C,hC,hCb⟩:=bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z hrootStop hrootTarget F hF hFm k
  exact ((UncutHistoryMass.weight_integrable (Base (0,0)) ν k).const_mul C).mono'
    ((measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z hrootStop hrootTarget F hF hFm k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (ae_of_all _ (fun h=>hCb (ω,h)))
end SHE.MixedOrdinaryErrorPrimitive
