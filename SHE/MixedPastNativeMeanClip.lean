module

public import SHE.MixedPastNativeMeanCap
public import SHE.NativeCarrierGeometry
public import SHE.ControlledRelativeScoreForest
public import SHE.ControlledThetaNativeGradient
public import SHE.MixedPastNativeConsistentPoint
public import SHE.MixedPastTwoFreshCovarianceInput
public import SHE.NativeResidualInputApplicability
public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastProfileDerivative
public import SHE.ControlledThetaNativeCovariance
public import SHE.ActualCovarianceMarkFields
public import SHE.MixedPastCovarianceMass
public import SHE.ControlledThetaRelativeCovarianceMark
public import SHE.MixedPastLiteralPoint
public import SHE.ControlledThetaRelativeArrays
public import SHE.ControlledThetaWeightedFields
public import SHE.MixedPastDecayedWord
public import SHE.RelativeHistoryGeometry
public import SHE.ParentHeatFields
public import SHE.MixedPastActualMean
public import SHE.MixedPastJointData
public import SHE.MixedNativeJointHistory
public import SHE.ControlledJointMeanIdentity
public import SHE.CarrierStopBounds
public import SHE.CoveredControlledLaw
public import SHE.JointWordAnalytic
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeMeanClip
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastNativeMeanClip_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastNativeMeanClip_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastNativeMeanClip_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastNativeMeanClip_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastNativeMeanClip_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastNativeMeanClip_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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


local instance mixedPastNativeMeanClip_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastNativeMeanClip_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open ProfileStability ProfileL2
open scoped BigOperators
local instance mixedPastNativeMeanClip_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v

/-- The ORIGINAL recursively generated native gradient endpoint change
has the clipped true-current gain on one history event before all past
and sample substitutions. Its remaining residual is exactly endpoint
minus the complete mean packet, for the physical three-leg FTC. -/
theorem actual_clip_ae (hΛ:0≤Λ)
    (hrootNative:∀x i,(Z.observations x i).stop=(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon) (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀p:ℕ,0<p→∀χ:ℝ,0≤χ→χ≤1→
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let a:=fun i=>NativeHeatSpan.unitCenter (centers Zero k h i)
      let D:=directions Zero ((carrier Zero k).observations.observations h) k h
      let R:=NativeFirstScoreReserve.covariance P target target (centers Zero k h) ((q:ℝ)-(v:ℝ))
      ∀E:WordRecursion.State (n+k),E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range→∀ω:Ω,
      let mean:=fun θ=>MixedPastNativeConsistentPoint.meanField
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q ω h
      let Point:=fun θ=>fderiv ℝ (ActualMeanKernel.cappedAverage
        (Base (θ,(U ω,Dir ω))) k q h) (mean θ) E
      let V:=PhysicalMeanRange.dampedDirection target target a ((q:ℝ)-(v:ℝ)) Λ
        (embed (S.second q ω-S.first q ω))
      let MP:=fun θ=>TwoFreshCompleteWord.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
        target target (centers Zero k h) lo hi (mean θ) false D E V
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
      let old:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero (fun x i=>(hrootNative x i).le) k h hp) (centers Zero k h)
      let T:=MixedPastWordMoments.total (d:=n) P lo hi
        (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
      let G:=MixedPastNativePacketUniform.packet 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
        (r:=k) P v q target target a (leafIndex k (fun i=>i)) p (ω,0)
      let Dcur:=MixedNativeDampedScoreAmplitude.amplitude 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
        P v q target a lo hi (ω,0)
      Integrable MP MixedNativeDampedScoreAmplitude.thetaMeasure ∧
        |Point 1-Point 0|≤2*(old*Real.sqrt (scoreVariance R E)*T)*(Dcur^χ*G)+
          |Point 1-Point 0-(∫θ,MP θ ∂MixedNativeDampedScoreAmplitude.thetaMeasure)|:=by
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=fun x i=>(hrootNative x i).le
  filter_upwards [ControlledRelativeScoreForest.all_inputs_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaNativeGradient.gradient_all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hforest hgradient
  intro q hvq hqt hp hsmall A0 ν hA0 hν hjet p hp0 χ hχ hχ1 target lo hi a D R E hE ω
    mean Point V MP old T G Dcur
  have hqv:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  have hn:stops Zero k h=targets Zero k h:=NativeCarrierGeometry.stops_eq_targets Zero
    hrootNative hrootStop k h
  have hσ:(fun i=>stops Zero k h i-(v:ℝ))=target:=by rw [hn]
  have hcenter:StoppedGaussianScore.nativeCenter (fun i=>a i+(0:UnitAddCircle))=centers Zero k h:=by
    funext i
    simp only [add_zero]
    exact NativeHeatSpan.scale_inverse _
  have hcenter0:StoppedGaussianScore.nativeCenter a=centers Zero k h:=by simpa only [add_zero] using hcenter
  have hgap(i:Fin (n+k)):(q:ℝ)-(v:ℝ)<target i:=
    sub_lt_sub_right (carrier_targets_after Zero h hages hqt i) _
  have ht1(i:Fin (n+k)):target i≤1:=by
    change targets Zero k h i-(v:ℝ)≤1
    rw [←hn]
    exact (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k h i).trans
      (hspan.trans P.horizon_le_one)
  have hlo(j:Fin k):(q:ℝ)-(v:ℝ)≤lo j:=sub_le_sub_right (hqt.le.trans (terminal_le_lower Zero k h j)) _
  have hinterval(j:Fin k):lo j<hi j:=sub_lt_sub_right (lower_lt_upper Zero k h hp j) _
  have hstops(j:Fin k)(i:Fin (n+k)):target i≤lo j ∨ hi j≤target i:=by
    have hh:=RelativeHistoryGeometry.relative_stop_dichotomy Zero k h j i
    change stops Zero k h i-(v:ℝ)≤lower Zero k h j-(v:ℝ) ∨
      upper Zero k h j-(v:ℝ)≤stops Zero k h i-(v:ℝ) at hh
    rw [hn] at hh
    exact hh
  have hdj(j l:Fin k)(hne:j≠l):hi j≤lo l ∨ hi l≤lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have ht(j:Fin k):target (leafIndex k (fun i=>i) j)∈Ioc 0 P.horizon:=
    RelativeHistoryGeometry.native_leaf_relative_age Zero (b:ℝ) P.horizon (fun _=>le_rfl) hspan k h hp hqv hqt j
  have hfr:=hforest q hqv hqt.le (U ω,Dir ω)
  rw [hσ] at hfr
  have hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (OldIntervalCovariance.familyCovariance target target
        (StoppedGaussianScore.nativeCenter (fun i=>a i+(0:UnitAddCircle)))
        (referenceProfile P Λ (U ω) (Dir ω)) lo hi j)).range:=by
    simpa only [hcenter] using hfr.1
  have hK:0≤old:=(hfr.2 hp hsmall).1
  have hgeom:|(∏j,scoreVariance (OldIntervalCovariance.familyCovariance target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+(0:UnitAddCircle)))
      (referenceProfile P Λ (U ω) (Dir ω)) lo hi j) (D j))*
      Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P target target
        (StoppedGaussianScore.nativeCenter (fun i=>a i+(0:UnitAddCircle))) ((q:ℝ)-(v:ℝ))) E)|≤
      old*Real.sqrt (scoreVariance R E):=by
    rw [hcenter,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hfr.2 hp hsmall).2 (Real.sqrt_nonneg _)
  have he0:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P target target
      (StoppedGaussianScore.nativeCenter (fun i=>a i+(0:UnitAddCircle))) ((q:ℝ)-(v:ℝ)))).range:=by
    simpa only [hcenter] using hE
  have hc:=MixedPastNativeMeanCap.clipped 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P hΛ v q hvq target a hgap ht1 lo hi hlo hinterval hstops hdj (leafIndex k (fun i=>i)) ht
    D E (ω,0) hD he0 (rootSelector k (fun i=>i)) (F (rootParameter k h))
    ((hF.smooth _).continuous.measurable) hA0 hν ((hF.smooth _).of_le (by simp)) hjet p hp0
    (old*Real.sqrt (scoreVariance R E)) (mul_nonneg hK (Real.sqrt_nonneg _)) hgeom χ hχ hχ1
  have hm(θ:ℝ):MixedPastNativePacketEnergy.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
      I₀ I₁ u₀ u₀ S v q target target a (θ,(ω,0))=mean θ:=by
    unfold MixedPastNativePacketEnergy.meanField mean MixedPastNativeConsistentPoint.meanField
    rw [hcenter,hn]
  have hwp(θ:ℝ):Point θ=NativeFirstWholeComplete.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
      target target (centers Zero k h) lo hi (mean θ) D E
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
    let aθ:ℝ×Inputs:=(θ,(U ω,Dir ω))
    have hR:NativeFirstScoreReserve.covariance P (stops (Base aθ) k h) (targets (Base aθ) k h)
        (centers (Base aθ) k h) q=R:=by
      rw [ControlledThetaRelativeDerivative.stops_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.targets_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.centers_eq P haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h,
        ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q,hσ]
    have heθ:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (stops (Base aθ) k h) (targets (Base aθ) k h) (centers (Base aθ) k h) q)).range:=by rw [hR];exact hE
    have hg:=hgradient aθ q hqv hqt (mean θ) E heθ
    rw [hσ] at hg
    have hterm:(carrier (Base aθ) k).terminal h=(carrier Zero k).terminal h:=
      ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm aθ (0,(0,0)) k h
    have hqtθ:(q:ℝ)≤(carrier (Base aθ) k).terminal h:=by rw [hterm];exact hqt.le
    simpa only [Point,ActualMeanKernel.cappedAverage,min_eq_left hqtθ,aθ] using hg
  simpa only [add_zero,hcenter,hcenter0,hm,←hwp] using hc

end SHE.MixedPastNativeMeanClip
