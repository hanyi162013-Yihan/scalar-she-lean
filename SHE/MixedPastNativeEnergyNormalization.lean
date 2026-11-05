module
public import SHE.MixedPastNativeHaarEnergy
public import SHE.NativeHigherEnergyFactors

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MixedPastNativeEnergyNormalization
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeEnergyNormalization_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeEnergyNormalization_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeEnergyNormalization_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeEnergyNormalization_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeEnergyNormalization_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeEnergyNormalization_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastNativeEnergyNormalization_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeEnergyNormalization_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open HistoryProductMeasure
open scoped BigOperators
local instance mixedPastNativeEnergyNormalization_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

def currentCoefficient (k p:ℕ)(χ Cdim:ℝ)(B0:ℝ≥0):ℝ:=
  (Cdim/(3*P.lower/8))^χ *
    (MixedPastNativePacketUniform.constant P k k p*
      (1+2*(2:ℝ)^(((2*(p*(k+2)):ℕ):ℝ)*P.exponent)*
        ((k:ℝ)*(NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M)^P.exponent)))^(1/(p:ℝ))

def pastCoefficient (k:ℕ)(B0:ℝ≥0):ℝ:=
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent
  let A:=Real.sqrt (TwoFreshCompleteWord.momentConstant P k k 1 C0)
  let B:=ControlledProfile.sharpUnit P*((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)
  let d:=fun j=>Real.sqrt (NativeOmittedCompleteWord.momentConstant P k k j 1 C0)
  ((k:ℝ)+1)*((A*B/2)^2+∑j:Fin k,(d j*BaselineOriginalGain.unitCoefficient P)^2)

theorem currentCoefficient_nonneg (k p:ℕ)(χ Cdim:ℝ)(B0:ℝ≥0)
    (hCdim:0≤Cdim)(hκ0:0≤κ)(hM:0≤M):
    0≤currentCoefficient κ (M:=M) P k p χ Cdim B0:=by
  have hPc:=MixedPastNativePacketUniform.constant_nonneg P k k p
  have hlower:=P.lower_pos
  have hUpper:=ProfileVariance.upperConstant_pos
  have hN:0≤NativeHybridMoments.momentConstant (p*(k+2)) B0 κ M:=by
    unfold NativeHybridMoments.momentConstant
    positivity
  unfold currentCoefficient
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg hCdim (by positivity)) _)
    (Real.rpow_nonneg (mul_nonneg hPc (by positivity)) _)

theorem pastCoefficient_nonneg (k:ℕ)(B0:ℝ≥0):
    0≤pastCoefficient κ (M:=M) P k B0:=by
  unfold pastCoefficient
  positivity

/-- Exact current-gap and true-current-displacement powers of the
actual complete kernel budget. All remaining factors are structural. -/
theorem current_eq (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(p:ℕ)(χ Cdim:ℝ)(B0:ℝ≥0)
    (hCdim:0≤Cdim)(hδ:0<(carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(q:ℝ)):
    CurrentEnergy k q t p χ Cdim B0=
      currentCoefficient κ (M:=M) P k p χ Cdim B0*
        ((carrier Zero k).terminal (QuarterSpatialEvent.anchor k t)-(q:ℝ))^(-χ/2)*
        (∫ω,‖S.second q ω-S.first q ω‖^2 ∂μ)^χ :=by
  unfold MixedPastNativeKernelActual.currentEnergy currentCoefficient
  dsimp only
  have hlower:=P.lower_pos
  rw [NativeHigherEnergyFactors.current_factor
    (div_nonneg hCdim (by positivity)) (integral_nonneg (fun _=>sq_nonneg _)) hδ]
  ring

/-- Actual covariance and omitted-baseline past terms share the
integrable local-past exponent -1/2, with the true relative age. -/
theorem past_le (k:ℕ)(q:ℝ≥0)(t:Fin k→ℝ)(A0 ν:ℝ)(B0:ℝ≥0)
    (hgap:0<(q:ℝ)-(v:ℝ))(hgap1:(q:ℝ)-(v:ℝ)≤1):
    let a:=QuarterSpatialEvent.anchor k t
    let sharp:=MixedPastWordMoments.total (d:=1) P
      (fun j=>lower Zero k a j-(v:ℝ)) (fun j=>upper Zero k a j-(v:ℝ))
      (fun j=>targets Zero k a (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
    PastEnergy k q t A0 ν B0≤pastCoefficient κ (M:=M) P k B0*sharp^2*
      ((q:ℝ)-(v:ℝ))^(-(1/2:ℝ))*(∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ):=by
  intro a sharp
  unfold MixedPastNativeKernelActual.pastEnergy
  dsimp only
  let C0:=(k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent
  let A:=Real.sqrt (TwoFreshCompleteWord.momentConstant P k k 1 C0)
  let B:=ControlledProfile.sharpUnit P*((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)
  let d:=fun j:Fin k=>Real.sqrt (NativeOmittedCompleteWord.momentConstant P k k j 1 C0)
  let D:=∫ω,‖S.second v ω-S.first v ω‖^2 ∂μ
  have hD:0≤D:=integral_nonneg (fun _=>sq_nonneg _)
  change ((k:ℝ)+1)*
    ((A*(sharp/2))^2*
      (((ControlledProfile.sharpUnit P*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4))*
        ((((1+k:ℕ):ℝ)/(3*P.lower/8))*3))^2*D)+
      ∑j:Fin k,(d j)^2*
        (((BaselineOriginalGain.unitCoefficient P*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ)))*sharp)^2*D))≤
    pastCoefficient κ (M:=M) P k B0*sharp^2*((q:ℝ)-(v:ℝ))^(-(1/2:ℝ))*D
  have hcoef:pastCoefficient κ (M:=M) P k B0=
      ((k:ℝ)+1)*((A*B/2)^2+∑j:Fin k,(d j*BaselineOriginalGain.unitCoefficient P)^2):=rfl
  have hBfactor:(ControlledProfile.sharpUnit P*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4))*
      ((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)=B*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4):=by
    dsimp only [B]
    ring
  have hsum:(∑j:Fin k,(d j)^2*
      (((BaselineOriginalGain.unitCoefficient P*((q:ℝ)-(v:ℝ))^(-(1/4:ℝ)))*sharp)^2*D))=
      (∑j:Fin k,(d j*BaselineOriginalGain.unitCoefficient P)^2)*
        ((((q:ℝ)-(v:ℝ))^(-(1/4:ℝ))*sharp)^2*D):=by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcoef,hBfactor,hsum]
  have hh:=NativeHigherEnergyFactors.past_factor P.exponent ((q:ℝ)-(v:ℝ)) D sharp A B
    (fun j=>d j*BaselineOriginalGain.unitCoefficient P) P.exponent_pos.le hgap hgap1 hD
  have hm:=mul_le_mul_of_nonneg_left hh (by positivity : 0≤(k:ℝ)+1)
  convert! hm using 1 <;> ring

end SHE.MixedPastNativeEnergyNormalization
