module

public import SHE.MixedPastCompleteCovarianceMoments
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.MixedPastLiteralCovariance
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastLiteralCovariance_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastLiteralCovariance_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastLiteralCovariance_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastLiteralCovariance_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastLiteralCovariance_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastLiteralCovariance_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastLiteralCovariance_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastLiteralCovariance_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastLiteralCovariance_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

def point (k : ℕ) (θ : ℝ) (q : ℝ≥0) (h : History X k)
    (e : Ω×StoppedGaussianFeatures.Domain→ℝ) (ω : Ω) : ℝ :=
  ActualCovarianceMarkFields.point (Base (θ,(U ω,Dir ω))) (oldProfile P Λ v (U ω,Dir ω))
    (ObservationTimeShift.profile (v:ℝ) (fun x=>e (ω,x))) k q
    (MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q ω h) h

include hIJ₀ hIJ₁ in
/-- Literal complete recursive covariance mark at the actual mixed
theta-current and random past reference. All Gaussian ranges, physical
old-score forest factors and exact full-residual assignment identities
are discharged on one parameter-independent history event. The only
remaining input quantity is the true past-measurable continuum score
mass, which can be estimated by the proved profile one-input energy. -/
theorem even_moment_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ hp : StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀ order : ℕ,0<order→∀ B0 : ℝ≥0,StandardTerminalBDGPower (order*(k+2)) J B0→
      ∀ e : Ω×StoppedGaussianFeatures.Domain→ℝ,Measurable e→
      @Measurable (Ω×StoppedGaussianFeatures.Domain) ℝ
        ((𝓕 v).prod inferInstance) inferInstance e→
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let B:=fun ω=>ControlledFixedReserve.covariance P Λ (U ω) (Dir ω)
        (fixedProfile P Λ (U ω) (Dir ω) lo hi) σ target (centers Zero k h) ((q:ℝ)-(v:ℝ)) θ
      let mass:=fun ω=>∫ x,|e (ω,x)| *scoreVariance (B ω)
        (StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) x)
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))
      (∀ ω,Integrable (fun x=>|e (ω,x)| *scoreVariance (B ω)
        (StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) x))
          (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))))→
      Integrable (fun ω=>(mass ω)^(2*order)) μ→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=MixedPastWordMoments.total (d:=n) P lo hi
        (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
      let G:=point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP v b hvb
        Z htarget hstop F hF hFm k θ q h e
      Integrable (fun ω=>|G ω|^(2*order)) μ ∧ (∫ ω,|G ω|^(2*order) ∂μ)≤
        MixedPastWordMoments.momentConstant P k k order
          ((k:ℝ)*(NativeHybridMoments.momentConstant (order*(k+2)) B0 κ M)^P.exponent)*
            (oldEnvelope*sharp/2)^(2*order)*(∫ ω,(mass ω)^(2*order) ∂μ) := by
  let ellOld:=fraction P*P.lower
  have hellOld : 0<ellOld:=mul_pos (fraction_pos P) P.lower_pos
  have hc (a : Inputs) : Measurable (oldProfile P Λ v a):=
    (ControlledReferenceWindows.coefficient_section_measurable P Λ 0 v a).const_mul (fraction P)
  have hcb (a:Inputs) (z:StoppedGaussianFeatures.Domain) : ellOld≤oldProfile P Λ v a z ∧ oldProfile P Λ v a z≤P.lower/2:=
    referenceProfile_bounds P Λ a.1 a.2 (z.1-(v:ℝ),z.2)
  have hfloor (z:StoppedGaussianFeatures.Domain) : ellOld≤(referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).reference z:=by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact ((he.1.trans he.2).trans (half_le_self P.lower_pos.le)).trans
      (ControlledReferenceWindows.coefficient_bounds P Λ 0 v (0,0) z).1
  filter_upwards [ControlledThetaRelativeCovarianceMark.mark_all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    uniform_all_profiles_forest_ae Zero hellOld hfloor (oldProfile P Λ v) hc hcb hages ρ k] with h hrep hforest
  intro q hvq hqH hqt hp hsmallOld θ hθ A0 ν hA0 hν hjet order horder B0 hBDG e he hepast
  intro σ target lo upper B mass hEnergy hMassI
  let center:=centers Zero k h
  let D:=directions Zero ((carrier Zero k).observations.observations h) k h
  let K:=timeWeight Zero ellOld (uniformConstant n) k h*
    OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
      (carrier_orderedTimes Zero hages k h hp) center
  have hK : 0≤K:=mul_nonneg
    (timeWeight_nonneg Zero hellOld (uniformConstant n) (fun j=>(uniformConstant_pos n j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hqv : (v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  have hspanq : (q:ℝ)-(v:ℝ)≤1:=by
    have hqb : (q:ℝ)≤(b:ℝ):=hqt.le.trans (terminal_le_initial Zero k h)
    linarith [P.horizon_le_one]
  have hsig (i) : 0<σ i:=RelativeHistoryGeometry.relative_stop_pos Zero k h hqv hqt i
  have hsig1 (i) : σ i≤1:=
    (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k h i).trans (hspan.trans P.horizon_le_one)
  have hage (i) : σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hgap (i) : (q:ℝ)-(v:ℝ)<target i:=sub_lt_sub_right (carrier_targets_after Zero h hages hqt i) _
  have hlo (j) : (q:ℝ)-(v:ℝ)≤lo j:=sub_le_sub_right (hqt.le.trans (terminal_le_lower Zero k h j)) _
  have hinterval (j) : lo j<upper j:=sub_lt_sub_right (lower_lt_upper Zero k h hp j) _
  have hstops (j i) : σ i≤lo j ∨ upper j≤σ i:=RelativeHistoryGeometry.relative_stop_dichotomy Zero k h j i
  have hdisjoint (j l) (hne:j≠l) : upper j≤lo l ∨ upper l≤lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hn (j) : σ (leafIndex k (fun i=>i) j)=target (leafIndex k (fun i=>i) j):=
    congrArg (fun z:ℝ=>z-(v:ℝ)) (RelativeHistoryGeometry.native_leaf Zero k h hp j)
  have ht (j) : target (leafIndex k (fun i=>i) j)∈Ioc 0 P.horizon:=
    RelativeHistoryGeometry.native_leaf_relative_age Zero (b:ℝ) P.horizon (fun _=>le_rfl) hspan k h hp hqv hqt j
  have hmatrix (a:Inputs) := ControlledThetaRelativeArrays.old_covariance_relative_fixed
    P haP Λ v b hvb Z htarget hstop F hF hFm (0,a) k h hqv hqt.le
  have hD (ω:Ω) (j:Fin k) : D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j)).range:=by
    have hh:=(hforest (U ω,Dir ω)).1 j
    rw [hmatrix (U ω,Dir ω)] at hh
    exact hh
  have hold (ω:Ω) : |∏ j,scoreVariance
      (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j)|≤K:=by
    have hh:=(hforest (U ω,Dir ω)).2 hp hsmallOld
    change (∏ j,scoreVariance (covariances Zero ((carrier Zero k).observations.observations h)
      (oldProfile P Λ v (U ω,Dir ω)) k h j) (D j))≤K at hh
    rw [hmatrix (U ω,Dir ω)] at hh
    have hnn : 0≤∏ j,scoreVariance
        (OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j) := by
      apply Finset.prod_nonneg
      intro j _
      exact scoreVariance_nonneg (OldIntervalCovariance.covariance_posSemidef σ target center hage
        (referenceProfile P Λ (U ω) (Dir ω)) (referenceProfile_measurable P Λ (U ω) (Dir ω))
        (fun z=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ (U ω) (Dir ω) z).1,
          (referenceProfile_bounds P Λ (U ω) (Dir ω) z).2⟩) (lo j) (upper j)) (hD ω j)
    simpa only [abs_of_nonneg hnn] using hh
  let c:=fun ω=>ControlledFixedReserve.coefficient P Λ (U ω) (Dir ω)
    (fixedProfile P Λ (U ω) (Dir ω) lo upper) θ
  have hcm (ω) : Measurable (c ω):=
    ((ControlledProfile.profile_measurable P Λ (U ω) (Dir ω)).comp
      (measurable_const.prodMk measurable_id)).sub (fixedProfile_measurable P Λ (U ω) (Dir ω) lo upper)
  have hbounds (ω) (z) : P.lower/2≤c ω z ∧ c ω z≤P.upper := by
    have hh:=ControlledFixedReserve.coefficient_bounds P Λ (U ω) (Dir ω)
      (fixedProfile P Λ (U ω) (Dir ω) lo upper)
      (fixedProfile_bounds P Λ (U ω) (Dir ω) lo upper hdisjoint) θ z
    constructor <;> linarith
  have hB (ω) : (B ω).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target center hage
    ((q:ℝ)-(v:ℝ)) (hcm ω) (fun z=>⟨(half_pos P.lower_pos).le.trans (hbounds ω z).1,(hbounds ω z).2⟩)
  have hranges:=FullResidualFrameRange.row_mem_all_ranges_ae σ target center hage ((q:ℝ)-(v:ℝ))
    c hcm (half_pos P.lower_pos) hbounds
  have hMassM:=MixedPastCovarianceMass.past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ
    (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) P v q σ target center lo upper
    (StoppedGaussianFeatures.stoppedRow σ target center)
    (StoppedGaussianFeatures.stoppedRow_measurable σ target center) e hepast
  have hmom:=MixedPastCompleteCovarianceMoments.input_moment
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ θ
    (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) P hlocal hΛ hθ v q hvq hqH hspanq
    σ target center hsig hsig1 hage hgap lo upper hlo hinterval hstops hdisjoint D hD
    (StoppedGaussianFeatures.stoppedRow σ target center)
    (StoppedGaussianFeatures.stoppedRow_measurable σ target center) hB
    (fun ω=>hranges.mono (fun _ hx=>hx ω)) (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) hn ht
    (F (rootParameter k h)) ((hF.smooth _).continuous.measurable) hA0 hν
    ((hF.smooth _).of_le (by simp)) hjet order horder B0 hBDG e he hEnergy K hK hold
    (hMassM.pow_const _) hMassI
  have heq (ω:Ω) : point 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q h e ω=
      (1/2:ℝ)*∫ x,e (ω,x)*PointwiseCompleteGaussianWord.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
        σ target center lo upper
        (MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v q σ target center ω)
        true D (StoppedGaussianFeatures.stoppedRow σ target center x)
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)) := by
    have htme:=ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm (θ,(U ω,Dir ω)) (0,(0,0)) k h
    rw [point,ActualCovarianceMarkFields.point_of_active _ _ _ _ _ _ _ (by simpa only [htme] using hqt)]
    exact hrep (θ,(U ω,Dir ω)) q hqv hqt (fun x=>e (ω,x)) _
  have hepow:=funext (fun ω=>congrArg (fun z:ℝ=>|z|^(2*order)) (heq ω))
  dsimp only at hmom ⊢
  rw [hepow]
  simpa only [K,ellOld,center,σ,target,lo,upper,D] using hmom

end SHE.MixedPastLiteralCovariance

