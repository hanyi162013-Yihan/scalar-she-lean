module
public import SHE.MixedNativeAverageFourierRows
public import SHE.NativeOriginalRowsEnergy
public import SHE.MixedNativeColumnFourierActions
public import SHE.MixedNativeSignedFourierAction
public import SHE.RootSectionFourierSwap

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false
namespace SHE.MixedNativeOriginalFourierRows
open AddCircle HistoryProductMeasure
open Set MeasureTheory PredictableL2 StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffCarriers SmoothCylinders UniformSmooth OrthogonalItoChannels FiniteHaar DyadicApproximation
  NativeHeatObservation NativeObservationNaturality
open scoped NNReal ENNReal
local instance mixedNativeOriginalFourierRows_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance mixedNativeOriginalFourierRows_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedNativeOriginalFourierRows_borel:BorelSpace CircleL2:=⟨rfl⟩
local instance mixedNativeOriginalFourierRows_realSigma:MeasurableSpace RealL2:=borel _
local instance mixedNativeOriginalFourierRows_realBorel:BorelSpace RealL2:=⟨rfl⟩
local instance mixedNativeOriginalFourierRows_rowSigma:MeasurableSpace RealHaarInput:=borel _
local instance mixedNativeOriginalFourierRows_rowBorel:BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedNativeOriginalFourierRows_blockSigma:MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedNativeOriginalFourierRows_blockBorel:BorelSpace (Both RealHaarInput):=⟨rfl⟩
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

/-- The actual native left source has the genuine post-past,
pre-terminal support of the original physical Ito input. -/
def left(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×Ω):NativeKernelHaarColumns.Space:=
  if v<z.1∧z.1<b then Left k z.1 hmass hρ z.2 else 0

/-- Both right-channel branches share the same genuine support. -/
def right(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(z:ℝ≥0×Ω):NativeKernelHaarColumns.Space:=
  if v<z.1∧z.1<b then Right k z.1 hmass hρ z.2 else 0

local notation "Source0"=>left 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm
local notation "Source1"=>right 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

local instance mixedNativeOriginalFourierRows_spaceSigma:MeasurableSpace NativeKernelHaarColumns.Space:=borel _
local instance mixedNativeOriginalFourierRows_spaceBorel:BorelSpace NativeKernelHaarColumns.Space:=⟨rfl⟩
local instance mixedNativeOriginalFourierRows_nativeSecond:SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

theorem left_measurable(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Source0 k hmass hρ):=by
  have hs:MeasurableSet {z:ℝ≥0×Ω|v<z.1∧z.1<b}:=
    (measurableSet_Ioo:MeasurableSet (Ioo v b)).preimage measurable_fst
  exact Measurable.ite
    hs
    (MixedPastNativeCompleteColumns.left_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k hmass hρ)
    measurable_const

theorem right_measurable(hΛ:0≤Λ)(k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ):Measurable (Source1 k hmass hρ):=by
  have hs:MeasurableSet {z:ℝ≥0×Ω|v<z.1∧z.1<b}:=
    (measurableSet_Ioo:MeasurableSet (Ioo v b)).preimage measurable_fst
  exact Measurable.ite
    hs
    (MixedPastNativeCompleteColumns.right_time_measurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm hΛ k hmass hρ)
    measurable_const

/-- Outside the physical window every scalar Fourier input whose raw
coordinates are the original averages is zero. This uses the actual raw
support, not a vanishing claim about the unguarded kernel extension. -/
theorem input_zero(k:ℕ)(q:ℝ≥0)(ω:Ω)(hq:¬(v<q∧q<b))
    (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ)(input:Both RealHaarInput)
    (hinput:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      ℓ input=∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
        RootSectionAverage.average R0 k (fun z=>ℓ (Raw k z.2 q z.1)) (ω,x) ∂haarAddCircle):input=0:=by
  have hz(h:History HeatCircle k):Raw k h q ω=0:=by
    unfold MixedNativeColumnRawFourier.raw
    apply MixedNativeRawSupport.off_active
    intro hh
    apply hq
    refine ⟨by exact_mod_cast hh.1,?_⟩
    have hb:(carrier Zero k).terminal h≤(b:ℝ):=(carrier Zero k).terminal_horizon h
    exact_mod_cast hh.2.trans_le hb
  have hc(ℓ:Both RealHaarInput→L[ℝ]ℝ):ℓ input=0:=by
    rw [hinput ℓ]
    simp only [RootSectionAverage.average,hz,map_zero,integral_zero,mul_zero]
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply lp.ext
    funext j
    exact hc (NativeJointColumnDirections.left j)
  · apply lp.ext
    funext j
    exact hc (NativeJointColumnDirections.right j)

/-- The actual raw Fourier input is the guarded complete native row,
with old-time L1 used only on the genuine physical window. -/
theorem input_eq
    (hΛ:0≤Λ)(hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ)(q:ℝ≥0)(ω:Ω){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (hSections:v<q∧q<b→
      Integrable (fun t=>Add k q hmass hρ (t,ω)) (Old k) ∧
      Integrable (fun t=>BaseCols k q hmass hρ (t,ω)) (Old k) ∧
      Integrable (fun t=>Signed k q hmass hρ (t,ω)) (Old k))
    (hCoord:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>ℓ (Raw k h q ω)) (historyMeasure R0 haarAddCircle k))
    (l:ℤ)(a:ℂ→L[ℝ]ℝ)(input:Both RealHaarInput)
    (hinput:∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      ℓ input=∫x:HeatCircle,NativeScalarFourierWeight.value ((mass+(l:ℝ)^2)^(-ρ/2)) a l x*
        RootSectionAverage.average R0 k (fun z=>ℓ (Raw k z.2 q z.1)) (ω,x) ∂haarAddCircle):
    input=WithLp.toLp 2
      (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source0 k hmass hρ (q,ω)),
       HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source1 k hmass hρ (q,ω))):=by
  by_cases hq:v<q∧q<b
  · unfold left right
    rw [if_pos hq,if_pos hq]
    exact (MixedNativeAverageFourierRows.row 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      J hIJ₀ hIJ₁ hnull hJ P haP v b hvb Z htarget hstop F hF hFm
      hΛ hages hrootStop k q (by exact_mod_cast hq.1) ω hmass hρ
      (hSections hq).1 (hSections hq).2.1 (hSections hq).2.2 hCoord l a input hinput).symm
  · rw [input_zero 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm k q ω hq _ a l input hinput]
    simp only [left,right,if_neg hq,map_zero]
    rfl

/-- Measurable equality-event Fubini lifts the fixed-current physical
row identity to the SAME original time/sample measure. No common
pointwise stochastic version in the current time is assumed. -/
theorem input_ae
    (hΛ:0≤Λ)(hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (k:ℕ){mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)
    (hSections:∀q:ℝ≥0,v<q→q<b→∀ᵐω∂μ,
      Integrable (fun t=>Add k q hmass hρ (t,ω)) (Old k) ∧
      Integrable (fun t=>BaseCols k q hmass hρ (t,ω)) (Old k) ∧
      Integrable (fun t=>Signed k q hmass hρ (t,ω)) (Old k))
    (hCoord:∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      Integrable (fun h=>ℓ (Raw k h z.1 z.2)) (historyMeasure R0 haarAddCircle k))
    (l:ℤ)(a:ℂ→L[ℝ]ℝ)(input:Process (E:=Both RealHaarInput) 𝓕 μ H)
    (hinput:∀ᵐz∂energyMeasure μ H,∀ℓ:Both RealHaarInput→L[ℝ]ℝ,
      ℓ (input z)=∫x:HeatCircle,NativeScalarFourierWeight.value ((mass+(l:ℝ)^2)^(-ρ/2)) a l x*
        RootSectionAverage.average R0 k (fun r=>ℓ (Raw k r.2 z.1 r.1)) (z.2,x) ∂haarAddCircle):
    input=ᵐ[energyMeasure μ H] fun z=>WithLp.toLp 2
      (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source0 k hmass hρ z),
       HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source1 k hmass hρ z)):=by
  let row:ℝ≥0×Ω→Both RealHaarInput:=fun z=>WithLp.toLp 2
    (HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source0 k hmass hρ z),
     HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l)) (Source1 k hmass hρ z))
  have hrow:Measurable row:=
    (WithLp.prod_continuous_toLp (p:=2) (α:=RealHaarInput) (β:=RealHaarInput)).measurable.comp
      ((((HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
        (left_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm k hmass hρ)).prodMk
       ((HilbertColumns.mapCLM (a.comp (NativeFourierNoiseRows.coefficient l))).continuous.measurable.comp
        (right_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
          P haP v b hvb Z htarget hstop F hF hFm hΛ k hmass hρ))))
  have hi:Measurable (input:ℝ≥0×Ω→Both RealHaarInput):=
    ((Lp.stronglyMeasurable input).mono (predictable_le_product 𝓕)).measurable
  have he:MeasurableSet {z:ℝ≥0×Ω|input z=row z}:=measurableSet_eq_fun hi hrow
  apply (Measure.ae_prod_iff_ae_ae he).mpr
  have hh:=Measure.ae_ae_of_ae_prod (hinput.and hCoord)
  filter_upwards [hh] with q hq
  by_cases hw:v<q∧q<b
  · filter_upwards [hq,hSections q hw.1 hw.2] with ω hω hs
    exact input_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hΛ hages hrootStop k q ω hmass hρ
      (fun _=>hs) hω.2 l a (input (q,ω)) hω.1
  · filter_upwards [hq] with ω hω
    exact input_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ
      P haP v b hvb Z htarget hstop F hF hFm hΛ hages hrootStop k q ω hmass hρ
      (fun h=>False.elim (hw h)) hω.2 l a (input (q,ω)) hω.1

end SHE.MixedNativeOriginalFourierRows

