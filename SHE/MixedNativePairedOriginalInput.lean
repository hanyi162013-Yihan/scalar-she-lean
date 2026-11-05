module
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
namespace SHE.MixedNativePairedOriginalInput
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
local notation "C1"=>MixedCanonicalWeightedPhysicalCoordinates.coordinate
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "C0"=>(fun k (ℓ:Both RealHaarInput→L[ℝ]ℝ) (z:(ℝ≥0×Ω)×History HeatCircle k)=>
  OrdinaryPhysicalCoordinates.coordinate modelU (Base0 (pastParameter z.1.2)) k ℓ (z.2,z.1))
local notation "Raw"=>MixedNativeColumnRawFourier.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P haP v b hvb Z ht hs F hF hFm
local notation "JointValue"=>MixedCanonicalNoiseIncrement.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P hAs 1 v b hvb Z ht hs F hF hFm
local notation "OrdinaryValue"=>MixedOrdinaryNoiseHilbert.value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm

include hrootStop hrootTarget in
theorem coordinate_pair(hA:P.coefficient=(fun z=>κ+aV z))(k:ℕ)
    (ℓ:Both RealHaarInput→L[ℝ]ℝ)(z:(ℝ≥0×Ω)×History HeatCircle k):
    C1 k ℓ z-C0 k ℓ z=ℓ (Raw k z.2 z.1.1 z.1.2):=by
  dsimp only [MixedCanonicalWeightedPhysicalCoordinates.coordinate]
  rw [←MixedUncutPhysicalColumns.coordinate_eq
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      (Base1 (pastParameter z.1.2)) k ℓ (z.2,z.1),
    ←OrdinaryPhysicalCoordinates.coordinate_eq modelU (Base0 (pastParameter z.1.2)) k ℓ (z.2,z.1),
    ←map_sub]
  congr 1
  unfold MixedNativeColumnRawFourier.raw ControlledReferenceThetaGeometry.level
  let G (A:{A:ℝ→ℝ // BoundedSmooth A}):Both RealHaarInput:=
    MixedUncutPhysicalGradient.raw
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      (ControlledReferenceFamilyLevel.level P A.1 A.2 Λ 1 v b hvb Z ht hs F hF hFm
        (pastParameter z.1.2)) k (z.2,z.1)-
    OrdinaryUncutPhysicalGradient.raw modelU
      (ControlledReferenceFamilyLevel.level P A.1 A.2 Λ 0 v b hvb Z ht hs F hF hFm
        (pastParameter z.1.2)) k (z.2,z.1)
  change G ⟨(fun z=>κ+aV z),hAs⟩=G ⟨P.coefficient,haP⟩
  exact congrArg G (Subtype.ext hA.symm)

variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include hIJ₀ hIJ₁ hnull hJ hrootStop hrootTarget hcenter hsmall in
/-- The actual joint-minus-ordinary kth native noise uses ONE original-J input.
On ONE original energy event every raw continuous-linear coordinate is L1
on the original history and equals that input's weighted root average. -/
theorem original_input_fourier(hA:P.coefficient=(fun z=>κ+aV z))
    (hlocal:StandardTerminalPastLocality J)(hL:1≤Λ){ρ:ℝ}(hρ:0≤ρ)
    (hbH:b≤H)(hb1:(b:ℝ)≤1)(hvb':v<b)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(k:ℕ):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      J.integral input=ᵐ[μ] (fun ω=>a (fourierCoeff
        (JointValue hL hρ k ω-OrdinaryValue hL hρ k ω) l))∧
      ∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
        Integrable (fun h=>ℓ (Raw k h z.1 z.2)) (historyMeasure R₀ AddCircle.haarAddCircle k)∧
        ℓ (input z)=∫x:HeatCircle,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l x*
          RootSectionAverage.average R₀ k
            (fun zh=>ℓ (Raw k zh.2 zh.1.1 zh.1.2)) (z,x) ∂AddCircle.haarAddCircle:=by
  obtain ⟨i1,hi1,hc1⟩:=MixedCanonicalNoiseIncrement.original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P hAs 1 v b hvb Z ht hs F hF hFm hsmall J hIJ₀ hIJ₁ hrootStop hrootTarget hcenter
    hnull hJ hlocal hL hρ hbH hb1 hvb' a l k
  obtain ⟨i0,hi0,hc0⟩:=MixedOrdinaryNoiseHilbert.original_input_fourier
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs 0 v b hvb Z hrootStop hrootTarget hcenter F hF hFm hsmall hL hρ
    hlocal hbH hb1 hvb' a l k
  have hmass1:=MixedCanonicalWeightedPhysicalCoordinates.coordinates_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
    P hAs 1 v b hvb Z ht hs F hF hFm (zero_le_one.trans hL) hbH hb1 AddCircle.haarAddCircle k
  have hmass0:=MixedOrdinaryCoordinateMass.coordinates_integrable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ hnull hJ
    P hAs 0 v b hvb Z hrootStop hrootTarget F hF hFm hbH hb1 AddCircle.haarAddCircle k
  have hm1:historyMeasure R1 (AddCircle.haarAddCircle:Measure HeatCircle) k=
      historyMeasure R₀ AddCircle.haarAddCircle k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=R1) (Q:=R₀) rfl rfl _ k
  have hm0:historyMeasure R0 (AddCircle.haarAddCircle:Measure HeatCircle) k=
      historyMeasure R₀ AddCircle.haarAddCircle k:=
    HistoryMeasureGeometry.historyMeasure_eq (R:=R0) (Q:=R₀) rfl rfl _ k
  rw [hm1] at hmass1
  rw [hm0] at hmass0
  refine ⟨i1-i0,?_,?_⟩
  · have hsJ:J.integral (i1-i0)=J.integral i1-J.integral i0:=map_sub J.integral i1 i0
    have he:=Lp.coeFn_sub (J.integral i1) (J.integral i0)
    rw [←hsJ] at he
    filter_upwards [hi1,hi0,he] with ω h1 h0 hh
    rw [hh,Pi.sub_apply,h1,h0]
    simpa only [ContinuousLinearMap.comp_apply,NativeMultiplierFourierIntegral.coefficient_apply] using
      (map_sub (a.comp (NativeFourierNoiseRows.coefficient l))
        (JointValue hL hρ k ω) (OrdinaryValue hL hρ k ω)).symm
  · have he:=ae_eq_of_ae_eq_trim (Lp.coeFn_sub i1 i0)
    filter_upwards [hc1,hc0,he,hmass1,hmass0] with z h1 h0 hz hmz1 hmz0 ℓ
    have hci1:Integrable (fun h=>C1 k ℓ (z,h)) (historyMeasure R₀ AddCircle.haarAddCircle k):=hmz1 ℓ
    have hci0:Integrable (fun h=>C0 k ℓ (z,h)) (historyMeasure R₀ AddCircle.haarAddCircle k):=
      (hmz0 ℓ).congr (ae_of_all _ (fun h=>
        OrdinaryPhysicalCoordinates.coordinate_eq modelU (Base0 (pastParameter z.2)) k ℓ (h,z)))
    have hpair:(fun zh=>C1 k ℓ zh-C0 k ℓ zh)=
        (fun zh=>ℓ (Raw k zh.2 zh.1.1 zh.1.2)):=by
      funext zh
      exact coordinate_pair 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P haP hAs v b hvb Z hrootStop hrootTarget F hF hFm hA k ℓ zh
    refine ⟨(hci1.sub hci0).congr (ae_of_all _ (fun h=>congrFun hpair (z,h))),?_⟩
    rw [hz]
    change ℓ (i1 z-i0 z)=_
    rw [map_sub,h1 ℓ,h0 ℓ]
    change (∫x,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l x*
        RootSectionAverage.average R₀ k (C1 k ℓ) (z,x) ∂AddCircle.haarAddCircle)-
      (∫x,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l x*
        RootSectionAverage.average R₀ k (C0 k ℓ) (z,x) ∂AddCircle.haarAddCircle)=_
    rw [RootSectionLinear.weighted_sub R₀ AddCircle.haarAddCircle k (C1 k ℓ) (C0 k ℓ) z
      hci1 hci0 (NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) a l)
      (NativeScalarFourierWeight.measurable _ _ _) (‖((Λ+(l:ℝ)^2)^(-ρ/2))‖*‖a‖)
      (NativeScalarFourierWeight.bound _ _ _),hpair]
end SHE.MixedNativePairedOriginalInput
