module

public import SHE.FirstGammaEndpointConstruction
public import SHE.FirstGammaConstruction
public import SHE.FirstGammaRows
public import SHE.RescaledRowsCoherence
public import SHE.FiniteSpliceStopCoherence
public import SHE.FirstGammaEndpointRows
public import SHE.SingularReferenceSplice
public import SHE.FullHorizonEndpointVersion
public import SHE.SingularInputBounds
public import SHE.MixedNativeFrozenPrefixIto
public import SHE.FirstGammaAffine
public import SHE.MixedNativeFrozenInterpolationRows
public import SHE.MixedNativeFrozenPrefixValues
public import SHE.FiniteReferenceSplicePast
public import SHE.StoppedInputAlgebra
public import SHE.PastFrozenPrefixRows
public import SHE.MixedPastJointData
public import SHE.FiniteReferenceSplice
public import SHE.MixedNativeJointPhysical
public import SHE.MixedNativePairMartingale
public import SHE.MixedNativeJointObservation
public import SHE.NativeJointPhysicalRows
public import SHE.NativeJointBracketDefect
public import SHE.NativeJointCovariance
public import SHE.NativeJointPhysicalStep

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000

namespace SHE.FirstGammaEndpointCoherence
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance firstGammaEndpointCoherence_realSigma : MeasurableSpace RealL2 := borel _
local instance firstGammaEndpointCoherence_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance firstGammaEndpointCoherence_circleSigma : MeasurableSpace CircleL2 := borel _
local instance firstGammaEndpointCoherence_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance firstGammaEndpointCoherence_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance firstGammaEndpointCoherence_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance firstGammaEndpointCoherence_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance firstGammaEndpointCoherence_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)



variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (P : CanonicalCovariance.ProfileParameters) (hκP : κ<P.lower)
variable (hΛ : 0≤Λ) (v b : ℝ≥0) (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hbH : b≤H)


open Set StoppedItoInputs
variable (θ : ℝ) (c : ℝ≥0) (hgap : ∀ i,(c:ℝ)<(Z i).target)
local notation "m0" => hell.le.trans ((hbU 0).1.trans (hbU 0).2)
local notation "R" => FirstGammaEndpointRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH
local notation "Rref" => FirstGammaEndpointRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ
local notation "Prefix" => FirstGammaRows.actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ c hgap
local notation "PrefRef" => FirstGammaRows.replacement 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v c hgap θ
local notation "Past" => MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "hPast" => MixedNativeFrozenPrefixIto.data_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

theorem actual_stop (hcb : c≤b) (i : Fin (n+n)) : stop 𝓕 μ H c (R i)=Prefix i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [FirstGammaEndpointRows.actual,FirstGammaRows.actual,MixedNativePairExtendedMartingale.rows,Fin.append_left,
      MixedNativePairObservedFirst.rows]
    rw [TwoChannelItoRows.stop_block]
    simp only [FirstGammaEndpointRows.additive,FirstGammaEndpointRows.first]
    rw [FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget j) (Z j).center hbH c hcb (hgap j),
      FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hell m0
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (htarget j) (Z j).center hbH c hcb (hgap j)]
  · let U:=FirstGammaEndpointRows.first 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH j
    let V:=FirstGammaEndpointRows.second 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z b htarget hbH j
    have he:=RescaledRowsCoherence.stop_rescaled 𝓕 μ H hΛ b c hcb U V
    simp only [FirstGammaEndpointRows.actual,Fin.append_right]
    change stop 𝓕 μ H c (InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b U V)=_
    have hu : stop 𝓕 μ H c U=NativeObservationProcess.process 𝓕 μ H hell m0
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (hgap j) (Z j).center :=
      FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hell m0
        (ContinuousHeatMild.coefficientFunction haU hell hbU S.first) S.first_coefficient (htarget j) (Z j).center hbH c hcb (hgap j)
    have hv : stop 𝓕 μ H c V=NativeObservationProcess.process 𝓕 μ H hell m0
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (hgap j) (Z j).center :=
      FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hell m0
        (ContinuousHeatMild.coefficientFunction haV hell hbV S.second) S.second_coefficient (htarget j) (Z j).center hbH c hcb (hgap j)
    rw [hu,hv] at he
    simpa only [FirstGammaRows.actual,MixedNativePairExtendedMartingale.rows,Fin.append_right,
      NativeHybridInput.rightLift,MixedNativePairLocalMartingale.row,MixedNativePairScaledMartingale.normalizedInput,
      MixedNativePairScaledMartingale.rowDifference,InterpolatedPredictableRows.rescaledDifference] using he

theorem replacement_stop (hcb : c≤b) (i : Fin (n+n)) : stop 𝓕 μ H c (Rref i)=PrefRef i := by
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [FirstGammaEndpointRows.replacement,FirstGammaRows.replacement,Fin.append_left,PastFrozenPrefixRows.rows]
    rw [TwoChannelItoRows.stop_block]
    simp only [FirstGammaEndpointRows.additive,FirstGammaEndpointRows.frozen]
    rw [FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const (htarget j) (Z j).center hbH c hcb (hgap j),
      FullHorizonEndpointVersion.stop_eq_prefix 𝓕 μ H b (sub_pos.mpr hκP)
        (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
        (FrozenReferenceFields.field P Λ κ θ hκP v Past)
        (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v Past hPast) (htarget j) (Z j).center hbH c hcb (hgap j)]
  · simp only [FirstGammaEndpointRows.replacement,FirstGammaRows.replacement,Fin.append_right]
    apply PastItoAlgebra.eq_of_ambient_ae
    filter_upwards [stop_ae 𝓕 μ H c (0:Process (E:=Both RealHaarInput) 𝓕 μ H),
      ae_eq_of_ae_eq_trim (Lp.coeFn_zero (Both RealHaarInput) 2
        ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hs hz
    rw [hs]
    by_cases hp : p∈before (Ω:=Ω) (c:ℝ)
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp,hz]
      rfl

theorem joint_stop (hcb : c≤b) (i : Fin ((n+n)+(n+n))) :
    stop 𝓕 μ H c
      (FirstGammaEndpointConstruction.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP hΛ v b htarget hbH θ i)=
    FiniteReferenceSplice.jointRows 𝓕 μ H v Prefix PrefRef i := by
  rw [FirstGammaEndpointConstruction.rows,SingularReferenceSplice.rows,StoppedInputAlgebra.stop_stop,
    min_eq_left (show (c:ℝ)≤(b:ℝ) by exact_mod_cast hcb),FiniteSpliceStopCoherence.stop_joint]
  have hR : (fun i=>stop 𝓕 μ H c (R i))=Prefix:=funext (actual_stop 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z hΛ b htarget hbH c hgap hcb)
  have hS : (fun i=>stop 𝓕 μ H c (Rref i))=PrefRef:=funext (replacement_stop 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z P hκP v b htarget hbH θ c hgap hcb)
  rw [hR,hS]

end SHE.FirstGammaEndpointCoherence
