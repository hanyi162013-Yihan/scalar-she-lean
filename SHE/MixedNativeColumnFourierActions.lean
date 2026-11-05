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

namespace SHE.MixedNativeColumnFourierActions
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedNativeColumnFourierActions_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedNativeColumnFourierActions_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeColumnFourierActions_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedNativeColumnFourierActions_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedNativeColumnFourierActions_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedNativeColumnFourierActions_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedNativeColumnFourierActions_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedNativeColumnFourierActions_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedNativeColumnFourierActions_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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
  MixedPastNativeKernel.difference MixedPastNativeHaarFields.columns

local notation "Diff"=>MixedPastNativeKernel.difference
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Columns"=>MixedPastNativeHaarFields.columns
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- Each actual old-space-averaged common-factor column has exactly
the Fourier coefficient of its original scalar physical input action.
This is a fixed old-time identity, before the stochastic isometry. -/
theorem common_realization (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(j:HaarNode)(l:ℤ):
    Integrable (fun z:(Fin k→HeatCircle)×HeatCircle=>
      (∫y:HeatCircle,(Diff k q q (separated k (z.2,t,z.1)) y ω:ℂ)*
        CircleNormalization.push (globalHaarColumn j (c (t,ω)).1) y ∂haarAddCircle).re)
      ((Measure.pi (fun _=>haarAddCircle)).prod haarAddCircle) ∧
    NativeFourierNoiseRows.coefficient l (Columns k q hmass hρ hm c (t,ω) j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          ((∫w:Fin k→HeatCircle,
            (∫y:HeatCircle,(Diff k q q (separated k (x,t,w)) y ω:ℂ)*
              CircleNormalization.push (globalHaarColumn j (c (t,ω)).1) y ∂haarAddCircle).re
            ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle:=by
  let ν:Measure (Fin k→HeatCircle):=Measure.pi (fun _=>haarAddCircle)
  let G:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)→ℂ:=fun z=>
    (Diff k q q (separated k (z.2.2,t,z.1)) z.2.1 ω:ℂ)
  have hsep:Measurable (fun z:(Fin k→HeatCircle)×(HeatCircle×HeatCircle)=>
      separated k (z.2.2,t,z.1)):=
    (separated_measurable k).comp (measurable_snd.snd.prodMk (measurable_const.prodMk measurable_fst))
  have hh:=Complex.continuous_ofReal.measurable.comp
    ((MixedPastNativeKernel.difference_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k q q).comp
        (((measurable_const (a:=ω)).prodMk hsep).prodMk measurable_snd.fst))
  have hG:Measurable G:=by convert! hh using 1
  obtain ⟨B,hB,hbound⟩:=MixedPastNativeKernel.difference_bound
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k q q t
  have hb:∀w y x,‖G (w,(y,x))‖≤B:=by
    intro w y x
    simpa only [G,Complex.norm_real,Real.norm_eq_abs] using hbound ω y x w
  refine ⟨NativeKernelRealFourierAverage.actions_integrable ν hG hB hb _,?_⟩
  have hf:=CircleNormalization.push_ae_property (globalHaarColumn j (c (t,ω)).1)
    (fun z:ℂ=>z.im=0) (globalHaarColumn_real_ae j (c (t,ω)).1 (c (t,ω)).2.1)
  let f:CircleL2:=CircleNormalization.push (globalHaarColumn j (c (t,ω)).1)
  have he:=NativeKernelRealFourierAverage.coefficient_average ν hG hB hb
    (fun _ _ _=>Complex.ofReal_im _) f hf hmass hρ l
  rw [MixedPastNativeHaarFields.columns_apply 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q hmass hρ hm c (t,ω) j]
  let Avg:Unit×(HeatCircle×HeatCircle)→ℂ:=fun z=>∫w,G (w,z.2) ∂ν
  have hop:NativeRandomKernel.integralOperator (Spatial k q q t) ω=
      NativeRandomKernel.integralOperator Avg ():=by
    apply NativeKernelCongruence.operator_congr
    intro y x
    unfold MixedPastNativeKernelAverage.spatial Avg G
    exact integral_complex_ofReal.symm
  rw [hop]
  exact he

theorem common_coefficient (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(ω:Ω)
    {mass ρ m Upper:ℝ}(hmass:1≤mass)(hρ:0≤ρ)(hm:0<m)
    (c:((Fin k→ℝ)×Ω)→EllipticField m Upper)(j:HaarNode)(l:ℤ):
    NativeFourierNoiseRows.coefficient l (Columns k q hmass hρ hm c (t,ω) j)=
      (((mass+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*
        ∫x:HeatCircle,fourier (-l) x*
          ((∫w:Fin k→HeatCircle,
            (∫y:HeatCircle,(Diff k q q (separated k (x,t,w)) y ω:ℂ)*
              CircleNormalization.push (globalHaarColumn j (c (t,ω)).1) y ∂haarAddCircle).re
            ∂Measure.pi (fun _=>haarAddCircle):ℝ):ℂ) ∂haarAddCircle:=
  (common_realization 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k q t ω hmass hρ hm c j l).2

end SHE.MixedNativeColumnFourierActions

