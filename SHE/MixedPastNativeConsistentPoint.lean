module

public import SHE.ControlledThetaNativeGradient
public import SHE.NativeReserveRowEnvelope
public import SHE.MixedPastNativeFirstWholeCompleteMoments
public import SHE.WeightedRowTimeShift
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastNativeConsistentPoint
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralPoint_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralPoint_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralPoint_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralPoint_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralPoint_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralPoint_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

open PastItoInputs PastItoAlgebra PhysicalProfile


local instance mixedPastLiteralPoint_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralPoint_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralPoint_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ) ≤ (Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v

/-- Actual entire theta-joint current, with the fixed original carrier
geometry and genuine relative observation ages based at the past v. -/
def meanField (k : ℕ) (θ : ℝ) (q : ℝ≥0) (ω : Ω) (h : History X k) : WordRecursion.State (n+k) :=
  MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q
    (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) ω

/-- Original native input kernel at the actual random past and current mean. -/
def point (k:ℕ)(θ:ℝ)(q:ℝ≥0)(r:ℝ)(h:History X k)(y:HeatCircle)(ω:Ω):ℝ:=
  ActualMeanKernel.rowPoint (Base (θ,(U ω,Dir ω))) k q r
    (meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb
      Z htarget hstop F hF hFm k θ q ω) h y

include hIJ₀ hIJ₁ in
/-- Complete conditional native cap for the ORIGINAL unweighted two-clock
kernel. Actual random past/current laws, all old ranges/forest factors and
native reserve applicability are discharged before the outer average. -/
theorem conditional_even_moment_ae
    (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∃Hf Cf:ℝ,0<Hf ∧ 0<Cf ∧
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ r : ℝ, (q:ℝ) ≤ r → r < (carrier Zero k).terminal h →
      (∀i,targets Zero k h i-r≤Hf)→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀θ:ℝ,|θ|≤1→∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀order:ℕ,0<order→∀B0:ℝ≥0,StandardTerminalBDGPower (order*(k+2)) J B0→
      ∀ᵐy:HeatCircle∂haarAddCircle,
      ∀weight:Ω→ℝ,Measurable[𝓕 v] weight→(∀ω,0≤weight ω)→Integrable weight μ→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let fresh:=sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal h-r)))*
        ∑i,sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k h i-r)) (centers Zero k h i) y‖
      let sharp:=MixedPastWordMoments.total (d:=n) P
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      let G:=point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q r h y
      Integrable (fun ω=>weight ω*|G ω|^(2*order)) μ ∧
        (∫ω,weight ω*|G ω|^(2*order) ∂μ)≤
          NativeFirstWholeComplete.momentConstant P k k order
            ((k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B0 κ M)^P.exponent)*
              (oldEnvelope*fresh*sharp)^(2*order)*(∫ω,weight ω ∂μ):=by
  obtain ⟨Hf,Cf,hHf,hCf,henv⟩:=NativeReserveRowEnvelope.sqrt_heat_envelope (n+k)
  refine ⟨Hf,Cf,hHf,hCf,?_⟩
  let ellOld:=fraction P*P.lower
  have hellOld : 0<ellOld:=mul_pos (fraction_pos P) P.lower_pos
  have hc (a : Inputs) : Measurable (oldProfile P Λ v a):=
    (ControlledReferenceWindows.coefficient_section_measurable P Λ 0 v a).const_mul (fraction P)
  have hcb (a:Inputs) (z:StoppedGaussianFeatures.Domain) : ellOld ≤ oldProfile P Λ v a z ∧ oldProfile P Λ v a z ≤ P.lower/2:=
    referenceProfile_bounds P Λ a.1 a.2 (z.1-(v:ℝ),z.2)
  have hfloor (z:StoppedGaussianFeatures.Domain) : ellOld ≤ (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).reference z:=by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact ((he.1.trans he.2).trans (half_le_self P.lower_pos.le)).trans
      (ControlledReferenceWindows.coefficient_bounds P Λ 0 v (0,0) z).1
  filter_upwards [ControlledThetaNativeGradient.rowPoint_all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    uniform_all_profiles_forest_ae Zero hellOld hfloor (oldProfile P Λ v) hc hcb hages ρ k]
    with h hrep hforest
  intro q hvq hqH hqt r hqr hrt hsmall hp hsmallOld θ hθ A0 ν hA0 hν hjet order horder B0 hBDG
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let upper:=fun j=>upper Zero k h j-(v:ℝ)
  let D:=directions Zero ((carrier Zero k).observations.observations h) k h
  let K:=timeWeight Zero ellOld (uniformConstant n) k h*
    OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
      (carrier_orderedTimes Zero hages k h hp) center
  have hK : 0 ≤ K:=mul_nonneg
    (timeWeight_nonneg Zero hellOld (uniformConstant n) (fun j=>(uniformConstant_pos n j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hqv : (v:ℝ) ≤ (q:ℝ):=by exact_mod_cast hvq
  have hqt0 : 0 ≤ (q:ℝ):=q.2
  have hqtle : (q:ℝ) ≤ (carrier Zero k).terminal h:=hqt.le
  have hspanq : (q:ℝ)-(v:ℝ) ≤ 1:=by
    have hqb : (q:ℝ) ≤ (b:ℝ):=hqt.le.trans (terminal_le_initial Zero k h)
    linarith [P.horizon_le_one]
  have hsig (i) : 0<σ i:=RelativeHistoryGeometry.relative_stop_pos Zero k h hqv hqt i
  have hsig1 (i) : σ i ≤ 1:=
    (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k h i).trans (hspan.trans P.horizon_le_one)
  have hage (i) : σ i ≤ target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hgap (i) : (q:ℝ)-(v:ℝ)<target i:=sub_lt_sub_right (carrier_targets_after Zero h hages hqt i) _
  have hlo (j) : (q:ℝ)-(v:ℝ) ≤ lo j:=sub_le_sub_right (hqt.le.trans (terminal_le_lower Zero k h j)) _
  have hinterval (j) : lo j<upper j:=sub_lt_sub_right (lower_lt_upper Zero k h hp j) _
  have hstops (j i) : σ i ≤ lo j ∨ upper j ≤ σ i:=RelativeHistoryGeometry.relative_stop_dichotomy Zero k h j i
  have hdisjoint (j l) (hne:j≠l) : upper j ≤ lo l ∨ upper l ≤ lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hn (j) : σ (leafIndex k (fun i=>i) j)=target (leafIndex k (fun i=>i) j):=
    congrArg (fun z:ℝ=>z-(v:ℝ)) (RelativeHistoryGeometry.native_leaf Zero k h hp j)
  have ht (j) : target (leafIndex k (fun i=>i) j)∈Ioc 0 P.horizon:=
    RelativeHistoryGeometry.native_leaf_relative_age Zero (b:ℝ) P.horizon (fun _=>le_rfl) hspan k h hp hqv hqt j
  have hmatrix (a:Inputs) := ControlledThetaRelativeArrays.old_covariance_relative_fixed
    P haP Λ v b hvb Z htarget hstop F hF hFm (0,a) k h hqv hqtle
  have hD (ω:Ω) (j:Fin k) : D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j)).range:=by
    have hh:=(hforest (U ω,Dir ω)).1 j
    rw [hmatrix (U ω,Dir ω)] at hh
    exact hh
  have hold (ω:Ω) : ∏ j,scoreVariance
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j) ≤ K:=by
    have hh:=(hforest (U ω,Dir ω)).2 hp hsmallOld
    change (∏ j,scoreVariance (covariances Zero ((carrier Zero k).observations.observations h)
      (oldProfile P Λ v (U ω,Dir ω)) k h j) (D j)) ≤ K at hh
    rw [hmatrix (U ω,Dir ω)] at hh
    exact hh
  let Q:Fin (n+k)→Observation:=(carrier Zero k).observations.observations h
  have hQage(i:Fin (n+k)):(Q i).stop≤(Q i).target:=
    RecursiveScoreSupport.carrier_ages Zero hages k h i
  have hQstop(i:Fin (n+k)):(carrier Zero k).terminal h≤(Q i).stop:=
    (carrier Zero k).stops_after h i
  have hQsmall(i:Fin (n+k)):(Q i).target-r≤Hf:=hsmall i
  have hstopEq:stops Zero k h=(fun i=>(Q i).stop):=by
    funext i
    exact min_eq_left (CarrierStopBounds.stop_le_initial Zero hrootStop k h i)
  have hNative:NativeFirstScoreReserve.covariance P (stops Zero k h) (targets Zero k h) center q=
      NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)):=
    ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q _ _ center
  have holdabs(ω:Ω):|∏j,scoreVariance
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j)|≤K:=by
    have hnon:0≤∏j,scoreVariance
        (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j):=by
      apply Finset.prod_nonneg
      intro j _
      apply scoreVariance_nonneg _ (hD ω j)
      exact OldIntervalCovariance.covariance_posSemidef σ target center hage _
        (referenceProfile_measurable P Λ (U ω) (Dir ω))
        (fun p=>⟨((mul_pos (fraction_pos P) P.lower_pos).le.trans
          (referenceProfile_bounds P Λ (U ω) (Dir ω) p).1),
            (referenceProfile_bounds P Λ (U ω) (Dir ω) p).2⟩) (lo j) (upper j)
    rw [abs_of_nonneg hnon]
    exact hold ω
  filter_upwards [henv P Q hQage q.2 hqr hrt hQstop hQsmall] with y hy
  intro weight hw hw0 hwi
  let E:=heatRow Q r y
  let fresh:=sqrt (Cf/((P.lower/8)*((carrier Zero k).terminal h-r)))*
    ∑i,sqrt ‖ProfileVariance.heatPhysical (4*(targets Zero k h i-r)) (centers Zero k h i) y‖
  have hfresh:0≤fresh:=mul_nonneg (sqrt_nonneg _) (Finset.sum_nonneg (fun _ _=>sqrt_nonneg _))
  have hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ)))).range:=by
    rw [←hNative,hstopEq]
    exact hy.1
  have hscore:sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)≤fresh:=by
    rw [←hNative,hstopEq]
    exact hy.2
  have hgeom(ω:Ω):|(∏j,scoreVariance
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j))*
        sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center ((q:ℝ)-(v:ℝ))) E)|≤K*fresh:=by
    rw [abs_mul,abs_of_nonneg (sqrt_nonneg _)]
    exact mul_le_mul (holdabs ω) hscore (sqrt_nonneg _) hK
  have hmoment:=MixedPastNativeFirstWholeCompleteMoments.weighted_even_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ P hlocal hΛ hθ
    v q hvq hqH hspanq σ target center hsig hsig1 hage lo upper hlo hinterval hstops hdisjoint
    D E (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) hn ht
    (fun j=>hgap (leafIndex k (fun i=>i) j)) (F (rootParameter k h))
    ((hF.smooth _).continuous.measurable) hA0 hν ((hF.smooth _).of_le (by simp)) hjet
    order horder B0 hBDG weight hw hw0 hwi (K*fresh) (mul_nonneg hK hfresh) hD hE
    (ae_of_all _ hgeom)
  have hpoint(ω:Ω):point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q r h y ω=
      NativeFirstWholeComplete.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
        σ target center lo upper
        (MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω)
        D E (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
    let a:ℝ×Inputs:=(θ,(U ω,Dir ω))
    have hobs:=ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h
    have hrow:heatRow ((carrier (Base a) k).observations.observations h) r y=E:=by rw [hobs]
    have hErange:heatRow ((carrier (Base a) k).observations.observations h) r y∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
          (stops (Base a) k h) (targets (Base a) k h) (centers (Base a) k h) q)).range:=by
      rw [ControlledThetaRelativeDerivative.stops_eq P haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.targets_eq P haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h,
        ControlledThetaRelativeDerivative.centers_eq P haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h,
        hrow,hNative]
      exact hE
    have hh:=hrep a q r hqv hqt hrt
      (meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb
        Z htarget hstop F hF hFm k θ q ω) y hErange
    rw [hrow] at hh
    exact hh
  dsimp only at hmoment ⊢
  simp_rw [hpoint]
  convert! hmoment using 1 <;> rfl

end SHE.MixedPastNativeConsistentPoint
