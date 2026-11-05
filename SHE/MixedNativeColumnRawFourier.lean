module
public import SHE.MixedNativeRawActions
public import SHE.MixedNativeColumnFourierActions
public import SHE.MixedNativeSignedFourierAction
public import SHE.RootSectionFourierSwap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeColumnRawFourier
open AddCircle HistoryProductMeasure
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativeColumnRawFourier_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeColumnRawFourier_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeColumnRawFourier_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeColumnRawFourier_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeColumnRawFourier_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeColumnRawFourier_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeColumnRawFourier_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeColumnRawFourier_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeColumnRawFourier_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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
local notation "dU"=>MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family HeatCircle 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)(hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:HeatCircle→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "pastParameter"=>MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Joint"=>(fun k h q ω=>MixedUncutPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S (Base (1,pastParameter ω)) k (h,(q,ω)))
local notation "Ordinary"=>(fun k h q ω=>OrdinaryUncutPhysicalGradient.raw modelU
  (Base (0,pastParameter ω)) k (h,(q,ω)))
local notation "Diff"=>MixedPastNativeKernel.difference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Weighted"=>MixedPastLiteralPoint.point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

def raw(k:ℕ)(h:History HeatCircle k)(q:ℝ≥0)(ω:Ω):Both RealHaarInput:=
  Joint k h q ω-Ordinary k h q ω
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Add"=>MixedPastNativeOldTimeEnergy.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseCols"=>MixedPastNativeOldTimeEnergy.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Signed"=>MixedPastSignedEndpointFields.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
attribute [local irreducible] raw MixedPastNativeKernel.difference MixedPastLiteralPoint.point
  MixedPastNativeOldTimeEnergy.additive MixedPastNativeOldTimeEnergy.base MixedPastSignedEndpointFields.raw

/-- At every original old-time section, BOTH native noise channels
are the actual Fourier averages of the genuine paired physical raw
input. The signed endpoint term is included in the right channel. -/
theorem realization
    (hΛ:0≤Λ)(hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(q:ℝ≥0)(hvq:(v:ℝ)<(q:ℝ))(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(j:HaarNode)(l:ℤ):
    let w:ℂ:=((mass+(l:ℝ)^2)^(-ρ/2):ℝ)
    Integrable (fun z:(Fin k→HeatCircle)×HeatCircle=>NativeJointColumnDirections.left j
      (Raw k (separated k (z.2,t,z.1)) q ω)) ((Measure.pi (fun _=>haarAddCircle)).prod haarAddCircle) ∧
    Integrable (fun z:(Fin k→HeatCircle)×HeatCircle=>NativeJointColumnDirections.right j
      (Raw k (separated k (z.2,t,z.1)) q ω)) ((Measure.pi (fun _=>haarAddCircle)).prod haarAddCircle) ∧
    NativeFourierNoiseRows.coefficient l (Add k q hmass hρ (t,ω) j)=
      w*∫x:HeatCircle,fourier (-l) x*
        ((∫a:Fin k→HeatCircle,NativeJointColumnDirections.left j
          (Raw k (separated k (x,t,a)) q ω) ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle ∧
    NativeFourierNoiseRows.coefficient l ((BaseCols k q hmass hρ (t,ω)+Signed k q hmass hρ (t,ω)) j)=
      w*∫x:HeatCircle,fourier (-l) x*
        ((∫a:Fin k→HeatCircle,NativeJointColumnDirections.right j
          (Raw k (separated k (x,t,a)) q ω) ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle:=by
  intro w
  let ν:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>haarAddCircle)
  let f0:=CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1)
  let fU:=CircleNormalization.push (globalHaarColumn j (CU (q,ω)).1)
  let fD:=CircleNormalization.push (globalHaarColumn j (CV (q,ω)).1-globalHaarColumn j (CU (q,ω)).1)
  let A0:(Fin k→HeatCircle)×HeatCircle→ℝ:=fun z=>
    (∫y:HeatCircle,(Diff k q q (separated k (z.2,t,z.1)) y ω:ℂ)*f0 y ∂haarAddCircle).re
  let AU:(Fin k→HeatCircle)×HeatCircle→ℝ:=fun z=>
    (∫y:HeatCircle,(Diff k q q (separated k (z.2,t,z.1)) y ω:ℂ)*fU y ∂haarAddCircle).re
  let AS:(Fin k→HeatCircle)×HeatCircle→ℝ:=fun z=>
    (∫y:HeatCircle,(Weighted k 1 q q (separated k (z.2,t,z.1)) y ω:ℂ)*fD y ∂haarAddCircle).re
  obtain ⟨hi0,h0⟩:=MixedNativeColumnFourierActions.common_realization
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k q t ω hmass hρ hκ (fun _=>AdditiveHaarForcing.constantField κ hκ) j l
  obtain ⟨hiU,hU⟩:=MixedNativeColumnFourierActions.common_realization
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    k q t ω hmass hρ hell (fun z=>CU (q,z.2)) j l
  obtain ⟨hiS,hS⟩:=MixedNativeSignedFourierAction.realization
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
    hΛ k q t ω hmass hρ j l
  have hchan(a:Fin k→HeatCircle)(x:HeatCircle):
      NativeJointColumnDirections.left j (Raw k (separated k (x,t,a)) q ω)=A0 (a,x)∧
      NativeJointColumnDirections.right j (Raw k (separated k (x,t,a)) q ω)=AU (a,x)+AS (a,x):=by
    simpa only [raw,A0,AU,AS,f0,fU,fD,map_sub] using
      MixedNativeRawActions.channels 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
        P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k (separated k (x,t,a)) q ω hvq j
  refine ⟨hi0.congr (ae_of_all _ (fun z=>(hchan z.1 z.2).1.symm)),
    (hiU.add hiS).congr (ae_of_all _ (fun z=>(hchan z.1 z.2).2.symm)),?_,?_⟩
  · change NativeFourierNoiseRows.coefficient l (Add k q hmass hρ (t,ω) j)=_
    unfold MixedPastNativeOldTimeEnergy.additive
    rw [h0]
    congr 1
    apply integral_congr_ae
    refine ae_of_all _ (fun x=>?_)
    exact congrArg (fun r:ℝ=>fourier (-l) x*(r:ℂ))
      (integral_congr_ae (ae_of_all ν (fun a=>(hchan a x).1.symm)))
  · have hiUC:Integrable (fun x:HeatCircle=>fourier (-l) x*((∫a,AU (a,x) ∂ν:ℝ):ℂ)) haarAddCircle:=
      (Complex.ofRealCLM.integrable_comp hiU.integral_prod_right).bdd_mul
        (fourier (-l)).continuous.measurable.aestronglyMeasurable
        (ae_of_all _ (fun x=>show ‖fourier (-l) x‖≤(1:ℝ) by simp [fourier_apply]))
    have hiSC:Integrable (fun x:HeatCircle=>fourier (-l) x*((∫a,AS (a,x) ∂ν:ℝ):ℂ)) haarAddCircle:=
      (Complex.ofRealCLM.integrable_comp hiS.integral_prod_right).bdd_mul
        (fourier (-l)).continuous.measurable.aestronglyMeasurable
        (ae_of_all _ (fun x=>show ‖fourier (-l) x‖≤(1:ℝ) by simp [fourier_apply]))
    simp only [lp.coeFn_add,Pi.add_apply,map_add]
    change NativeFourierNoiseRows.coefficient l (BaseCols k q hmass hρ (t,ω) j)+
      NativeFourierNoiseRows.coefficient l (Signed k q hmass hρ (t,ω) j)=_
    unfold MixedPastNativeOldTimeEnergy.base
    rw [hU,hS,←mul_add,←integral_add hiUC hiSC]
    congr 1
    apply integral_congr_ae
    filter_upwards [hiU.prod_left_ae,hiS.prod_left_ae] with x hxU hxS
    rw [←mul_add,←Complex.ofReal_add,←integral_add hxU hxS]
    congr 1
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun a=>(hchan a x).2.symm)

end SHE.MixedNativeColumnRawFourier

