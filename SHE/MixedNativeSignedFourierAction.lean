module
public import SHE.MixedPastNativeCompleteColumns
public import SHE.NativeKernelRealFourierAverage
public import SHE.MixedNativeRawDifference
public import SHE.NativeKernelHaarColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedNativeSignedFourierAction
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeSignedFourierAction_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeSignedFourierAction_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeSignedFourierAction_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeSignedFourierAction_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeSignedFourierAction_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeSignedFourierAction_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedNativeSignedFourierAction_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeSignedFourierAction_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeSignedFourierAction_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

local notation "Field"=>MixedPastNativeKernel.field
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Frame"=>MixedPastNativeKernelTrace.frame Λ P haP v b hvb Z htarget hstop F hF hFm

local notation "Current"=>MixedPastNativeKernelEnergy.current
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "RowVariance"=>MixedPastNativeKernelEnergy.rowVariance Λ P haP v b hvb Z htarget hstop F hF hFm
local notation "RowResidual"=>MixedPastNativeKernelEnergy.rowResidual
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "AAmp"=>MixedPastNativeAAmplitude.amplitude
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm


local notation "Spatial"=>MixedPastNativeKernelAverage.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "PastEnergy"=>MixedPastNativeKernelActual.pastEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CurrentEnergy"=>MixedPastNativeKernelActual.currentEnergy
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
attribute [local irreducible] MixedPastNativeKernel.field MixedPastNativeKernelAverage.spatial
  MixedPastNativeKernelActual.pastEnergy MixedPastNativeKernelActual.currentEnergy MixedPastWordMoments.total
  MixedPastLiteralPoint.point MixedPastSignedEndpointFields.raw MixedPastKernelFields.spatial

local notation "Diff"=>MixedPastNativeKernel.difference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Columns"=>MixedPastNativeHaarFields.columns
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point"=>MixedPastLiteralPoint.point
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Signed"=>MixedPastSignedEndpointFields.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "CU"=>ContinuousHeatMild.coefficientFunction haU hell hbU S.first
local notation "CV"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Endpoint"=>MixedPastKernelFields.spatial
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The stopped theta-one coefficient-difference columns retain their
literal original scalar input under old-space and Fourier averaging. -/
theorem realization (hΛ:0≤Λ)(k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(j:HaarNode)(l:ℤ):
    Integrable (fun z:(Fin k→HeatCircle)×HeatCircle=>
      (∫y:HeatCircle,(Point k 1 q q (separated k (z.2,t,z.1)) y ω:ℂ)*
        CircleNormalization.push (globalHaarColumn j (CV (q,ω)).1-
          globalHaarColumn j (CU (q,ω)).1) y ∂haarAddCircle).re)
      ((Measure.pi (fun _=>haarAddCircle)).prod haarAddCircle) ∧
    NativeFourierNoiseRows.coefficient l (Signed k q hmass hρ (t,ω) j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          ((∫w:Fin k→HeatCircle,
            (∫y:HeatCircle,(Point k 1 q q (separated k (x,t,w)) y ω:ℂ)*
              CircleNormalization.push (globalHaarColumn j (CV (q,ω)).1-
                globalHaarColumn j (CU (q,ω)).1) y ∂haarAddCircle).re
            ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle:=by
  let ν:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>haarAddCircle)
  let G:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)→ℂ:=fun z=>
    (Point k 1 q q (separated k (z.2.2,t,z.1)) z.2.1 ω:ℂ)
  have hsep:Measurable (fun z:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)=>
      separated k (z.2.2,t,z.1)):=
    (separated_measurable k).comp (measurable_snd.snd.prodMk (measurable_const.prodMk measurable_fst))
  have hh:=Complex.continuous_ofReal.measurable.comp
    ((MixedPastLiteralFields.point_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k 1 q (fun _=>q) measurable_const).comp
        ((measurable_const (a:=ω)).prodMk (hsep.prodMk measurable_snd.fst)))
  have hG:Measurable G:=by convert! hh using 1
  obtain ⟨B,hB,hbound⟩:=ControlledFamilyKernelBounds.weightedPoint_family_uniform_bound
    P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm k hΛ q q t
  have hb:∀w y x,‖G (w,(y,x))‖≤B:=by
    intro w y x
    simpa only [G,Complex.norm_real,Real.norm_eq_abs,MixedPastLiteralPoint.point] using
      hbound (1,(U ω,Dir ω)) (MixedPastLiteralPoint.meanField
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm k 1 q ω) y x w
  let f:CircleL2:=CircleNormalization.push (globalHaarColumn j (CV (q,ω)).1-globalHaarColumn j (CU (q,ω)).1)
  refine ⟨NativeKernelRealFourierAverage.actions_integrable ν hG hB hb f,?_⟩
  have hf:∀ᵐy∂haarAddCircle,(f y).im=0:=by
    apply CircleNormalization.push_ae_property _ (fun z:ℂ=>z.im=0)
    filter_upwards [globalHaarColumn_real_ae j (CV (q,ω)).1 (CV (q,ω)).2.1,
      globalHaarColumn_real_ae j (CU (q,ω)).1 (CU (q,ω)).2.1,
      Lp.coeFn_sub (globalHaarColumn j (CV (q,ω)).1) (globalHaarColumn j (CU (q,ω)).1)] with y hd hc hs
    rw [hs]
    change (globalHaarColumn j (CV (q,ω)).1 y-globalHaarColumn j (CU (q,ω)).1 y).im=0
    simp only [Complex.sub_im,hd,hc,sub_self]
  have he:=NativeKernelRealFourierAverage.coefficient_average ν hG hB hb
    (fun _ _ _=>Complex.ofReal_im _) f hf hmass hρ l
  rw [MixedPastSignedEndpointFields.raw_section 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ t ω,SignedKernelColumns.rawColumns_apply]
  let Avg:Unit×(HeatCircle×HeatCircle)→ℂ:=fun z=>∫w,G (w,z.2) ∂ν
  have hop:NativeRandomKernel.integralOperator (Endpoint k 1 q q t) ω=
      NativeRandomKernel.integralOperator Avg ():=by
    apply NativeKernelCongruence.operator_congr
    intro y x
    unfold MixedPastKernelFields.spatial ActualMeanKernel.weightedSpatial Avg G MixedPastLiteralPoint.point
    exact integral_complex_ofReal.symm
  rw [hop]
  exact he

theorem coefficient (hΛ:0≤Λ)(k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(j:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l (Signed k q hmass hρ (t,ω) j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          ((∫w:Fin k→HeatCircle,
            (∫y:HeatCircle,(Point k 1 q q (separated k (x,t,w)) y ω:ℂ)*
              CircleNormalization.push (globalHaarColumn j (CV (q,ω)).1-
                globalHaarColumn j (CU (q,ω)).1) y ∂haarAddCircle).re
            ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle:=
  (realization 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm hΛ k q t ω hmass hρ j l).2

end SHE.MixedNativeSignedFourierAction

