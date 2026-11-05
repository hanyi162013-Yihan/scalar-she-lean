module
public import SHE.MixedNativeColumnRawFourier
public import SHE.MixedNativeColumnFourierActions
public import SHE.MixedNativeSignedFourierAction
public import SHE.RootSectionFourierSwap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeAverageFourierRows
open AddCircle HistoryProductMeasure
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativeAverageFourierRows_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeAverageFourierRows_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeAverageFourierRows_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeAverageFourierRows_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeAverageFourierRows_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeAverageFourierRows_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeAverageFourierRows_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeAverageFourierRows_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeAverageFourierRows_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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

local notation "Raw"=>MixedNativeColumnRawFourier.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Add"=>MixedPastNativeOldTimeEnergy.additive
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "BaseCols"=>MixedPastNativeOldTimeEnergy.base
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Signed"=>MixedPastSignedEndpointFields.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Left"=>MixedPastNativeCompleteColumns.left
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Right"=>MixedPastNativeCompleteColumns.right
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "R0"=>referenceData P P.coefficient haP Λ 0 v b hvb (0,0)
local notation "Old"=>(fun n:ℕ=>Measure.pi (fun _:Fin n=>volume.restrict (Ioc (v:ℝ) (b:ℝ))))
attribute [local irreducible] MixedNativeColumnRawFourier.raw MixedPastNativeCompleteColumns.left
  MixedPastNativeCompleteColumns.right MixedPastNativeOldTimeEnergy.additive MixedPastNativeOldTimeEnergy.base
  MixedPastSignedEndpointFields.raw

/-- Original old-time averaging preserves the exact real Fourier row
identity. All three Hilbert L1 sections and original-history coordinate
L1 are retained explicitly for the subsequent actual-model application. -/
theorem projections
    (hΛ:0≤Λ)(hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(q:ℝ≥0)(hvq:(v:ℝ)<(q:ℝ))(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (hAdd:Integrable (fun t=>Add k q hmass hρ (t,ω)) (Old k))
    (hBase:Integrable (fun t=>BaseCols k q hmass hρ (t,ω)) (Old k))
    (hSigned:Integrable (fun t=>Signed k q hmass hρ (t,ω)) (Old k))
    (hCoord:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>ℓ (Raw k h q ω)) (historyMeasure R0 haarAddCircle k))
    (j:HaarNode)(l:ℤ)(a:ℂ→L[ℝ]ℝ):
    let w:ℝ:=(mass+(l:ℝ)^2)^(-ρ/2)
    a (NativeFourierNoiseRows.coefficient l (Left k q hmass hρ ω j))=
      ∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
        RootSectionAverage.average R0 k (fun z=>NativeJointColumnDirections.left j (Raw k z.2 q z.1)) (ω,x)
        ∂haarAddCircle ∧
    a (NativeFourierNoiseRows.coefficient l (Right k q hmass hρ ω j))=
      ∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
        RootSectionAverage.average R0 k (fun z=>NativeJointColumnDirections.right j (Raw k z.2 q z.1)) (ω,x)
        ∂haarAddCircle:=by
  intro w
  have he(t:Fin k→ℝ):=
    MixedNativeColumnRawFourier.realization 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hnull hJ P haP v b hvb Z htarget hstop F hF hFm
      hΛ hages hrootStop k q hvq t ω hmass hρ j l
  have hproj(t:Fin k→ℝ):
      a (NativeFourierNoiseRows.coefficient l (Add k q hmass hρ (t,ω) j))=
        ∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
          (∫y:Fin k→HeatCircle,NativeJointColumnDirections.left j (Raw k (separated k (x,t,y)) q ω)
            ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle ∧
      a (NativeFourierNoiseRows.coefficient l ((BaseCols k q hmass hρ (t,ω)+Signed k q hmass hρ (t,ω)) j))=
        ∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
          (∫y:Fin k→HeatCircle,NativeJointColumnDirections.right j (Raw k (separated k (x,t,y)) q ω)
            ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle:=by
    constructor
    · rw [(he t).2.2.1]
      change a (w • fourierCoeff _ l)=_
      rw [map_smul]
      exact (NativeScalarFourierWeight.integral _ (he t).1.integral_prod_right w a l).symm
    · rw [(he t).2.2.2]
      change a (w • fourierCoeff _ l)=_
      rw [map_smul]
      exact (NativeScalarFourierWeight.integral _ (he t).2.1.integral_prod_right w a l).symm
  let Eval:NativeKernelHaarColumns.Space→L[ℝ]ℝ:=
    (a.comp (NativeFourierNoiseRows.coefficient l)).comp (lp.evalCLM ℝ (fun _:HaarNode=>CircleL2) 2 j)
  have hs0:=RootSectionFourierSwap.weighted R0 k
    (fun z=>NativeJointColumnDirections.left j (Raw k z.2 q z.1)) ω (hCoord (NativeJointColumnDirections.left j))
    (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
    (‖w‖*‖a‖) (NativeScalarFourierWeight.bound w a l)
  have hs1:=RootSectionFourierSwap.weighted R0 k
    (fun z=>NativeJointColumnDirections.right j (Raw k z.2 q z.1)) ω (hCoord (NativeJointColumnDirections.right j))
    (NativeScalarFourierWeight.value w a l) (NativeScalarFourierWeight.measurable w a l)
    (‖w‖*‖a‖) (NativeScalarFourierWeight.bound w a l)
  constructor
  · change Eval (Left k q hmass hρ ω)=_
    unfold MixedPastNativeCompleteColumns.left
    rw [←Eval.integral_comp_comm hAdd]
    calc
      _=∫t:Fin k→ℝ,∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
          (∫y:Fin k→HeatCircle,NativeJointColumnDirections.left j (Raw k (separated k (x,t,y)) q ω)
            ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle ∂Old k:=
        integral_congr_ae (ae_of_all _ (fun t=>(hproj t).1))
      _=_:=hs0.2.symm
  · change Eval (Right k q hmass hρ ω)=_
    unfold MixedPastNativeCompleteColumns.right
    have hSum:Integrable (fun t=>BaseCols k q hmass hρ (t,ω)+Signed k q hmass hρ (t,ω)) (Old k):=
      hBase.add hSigned
    rw [←integral_add hBase hSigned,←Eval.integral_comp_comm hSum]
    calc
      _=∫t:Fin k→ℝ,∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
          (∫y:Fin k→HeatCircle,NativeJointColumnDirections.right j (Raw k (separated k (x,t,y)) q ω)
            ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle ∂Old k:=
        integral_congr_ae (ae_of_all _ (fun t=>(hproj t).2))
      _=_:=hs1.2.symm

/-- The complete original scalar input is exactly the real-linear
Fourier row of the actual two native Hilbert column fields. -/
theorem row
    (hΛ:0≤Λ)(hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(q:ℝ≥0)(hvq:(v:ℝ)<(q:ℝ))(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (hAdd:Integrable (fun t=>Add k q hmass hρ (t,ω)) (Old k))
    (hBase:Integrable (fun t=>BaseCols k q hmass hρ (t,ω)) (Old k))
    (hSigned:Integrable (fun t=>Signed k q hmass hρ (t,ω)) (Old k))
    (hCoord:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>ℓ (Raw k h q ω)) (historyMeasure R0 haarAddCircle k))
    (l:ℤ)(a:ℂ→L[ℝ]ℝ)(input:Both RealHaarInput)
    (hinput:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      ℓ input=∫x:HeatCircle,NativeScalarFourierWeight.value ((mass+(l:ℝ)^2)^(-ρ/2)) a l x*
        RootSectionAverage.average R0 k (fun z=>ℓ (Raw k z.2 q z.1)) (ω,x) ∂haarAddCircle):
    WithLp.toLp 2
      (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Left k q hmass hρ ω),
       HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Right k q hmass hρ ω))=input:=by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply lp.ext
    funext j
    change a (NativeFourierNoiseRows.coefficient l (Left k q hmass hρ ω j))=
      NativeJointColumnDirections.left j input
    exact (projections 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hΛ hages hrootStop k q hvq ω hmass hρ
      hAdd hBase hSigned hCoord j l a).1.trans (hinput (NativeJointColumnDirections.left j)).symm
  · apply lp.ext
    funext j
    change a (NativeFourierNoiseRows.coefficient l (Right k q hmass hρ ω j))=
      NativeJointColumnDirections.right j input
    exact (projections 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hΛ hages hrootStop k q hvq ω hmass hρ
      hAdd hBase hSigned hCoord j l a).2.trans (hinput (NativeJointColumnDirections.right j)).symm

end SHE.MixedNativeAverageFourierRows

