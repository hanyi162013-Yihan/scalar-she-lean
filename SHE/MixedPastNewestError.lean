module
public import SHE.MixedPastBoundedCovarianceInput
public import SHE.ControlledFreshHolderMass
public import SHE.ControlledHessianRelative
public import SHE.AllProfileInstantScoreMass
public import SHE.MixedPastLiteralPoint

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
namespace SHE.MixedPastNewestError
open Set MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
  GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  FullResidualAssignedMoments GaussianDependentScores MeasurableGaussianScores PhysicalProfile
  WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry ControlledProfile ControlledReferenceLevel ControlledReferenceWindows
  ControlledFamilyProfileForest CoveredHistoryGeometry CoveredControlledLaw SmoothCylinders UniformSmooth
  GaussianConvolution
open scoped NNReal ENNReal BigOperators
local instance mixedPastNewestError_realSigma : MeasurableSpace RealL2:=borel _
local instance mixedPastNewestError_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance mixedPastNewestError_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance mixedPastNewestError_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance mixedPastNewestError_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance mixedPastNewestError_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance mixedPastNewestError_circleSigma : MeasurableSpace CircleL2:=borel _
local instance mixedPastNewestError_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance mixedPastNewestError_period : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {Ω:Type*}[MeasurableSpace Ω]{X:Type}[MeasurableSpace X]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (P:CanonicalCovariance.ProfileParameters)(haP:BoundedSmooth P.coefficient)
variable (v b:ℝ≥0)(hvb:v≤b)(Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "U"=>MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Dir"=>MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local notation "Mean"=>MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Literal newest physical error insertion. The multiplier is not
included in any Gaussian law or averaged auxiliary test. -/
def value (k:ℕ)(θ:ℝ)(q:ℝ≥0)(h:History X k)(e:Ω×HeatCircle→ℝ)(ω:Ω):ℝ:=
  let p:ℝ×Inputs:=(θ,(U ω,Dir ω))
  (1/2:ℝ)*∫y:HeatCircle,e (ω,y)*WordRecursion.directionalSecond
    (gaussianAverage (WordRecursion.covariance
      (referenceData P P.coefficient haP Λ p.1 v b hvb p.2).reference
      ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) (Mean k θ q ω h)
          (heatRow ((carrier (Base p) k).observations.observations h) q y) ∂haarAddCircle

attribute [local irreducible] value MeasurableGaussianScores.scoreVariance
  MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse

include hIJ₀ hIJ₁ in
/-- Sharp old-block second moment for the actual F_q-dependent newest
error. All physical range and random-past Gaussian applicability is
discharged; only its true uniform one-state cap ε is used. -/
theorem good_energy_ae (hlocal:StandardTerminalPastLocality J)(hΛ:0≤Λ)
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop:∀x i,(Z.observations x i).stop≤(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀q:ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀hp:StrictHistory Zero k h,SmallHistory Zero (uniformHorizon 1) k h→
      ∀θ:ℝ,|θ|≤1→∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀B0:ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      ∀ε:ℝ,0≤ε→∀e:Ω×HeatCircle→ℝ,Measurable e→(∀p,|e p|≤ε)→
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=MixedPastWordMoments.total (d:=1) P
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))
        (fun j=>targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ)) A0 ν
      let G:=value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P haP v b hvb Z htarget hstop F hF hFm k θ q h e
      Integrable (fun ω=>|G ω|^2) μ ∧ (∫ω,|G ω|^2 ∂μ)≤
        MixedPastWordMoments.momentConstant P k k 1
          ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
            (oldEnvelope*sharp*(ε*((1+k:ℕ):ℝ)/((P.lower/2)*((carrier Zero k).terminal h-q)))/2)^2 := by
  let ellOld:=fraction P*P.lower
  have hellOld:0<ellOld:=mul_pos (fraction_pos P) P.lower_pos
  have hc(a:Inputs):Measurable (oldProfile P Λ v a):=
    (coefficient_section_measurable P Λ 0 v a).const_mul (fraction P)
  have hcb(a:Inputs)(p:StoppedGaussianFeatures.Domain):ellOld≤oldProfile P Λ v a p ∧
      oldProfile P Λ v a p≤P.lower/2:=referenceProfile_bounds P Λ a.1 a.2 (p.1-v,p.2)
  have hfloor(p:StoppedGaussianFeatures.Domain):ellOld≤
      (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)).reference p:=by
    have he:=referenceProfile_bounds P Λ (0:CircleL2) 0 (0,0)
    exact ((he.1.trans he.2).trans (half_le_self P.lower_pos.le)).trans
      (coefficient_bounds P Λ 0 v (0,0) p).1
  filter_upwards [ControlledHessianRelative.all_parameters_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
      P haP Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    uniform_all_profiles_forest_ae Zero hellOld hfloor (oldProfile P Λ v) hc hcb hages ρ k]
    with h hrep hres hforest
  intro q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet B0 hBDG ε hε e he hecap
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let upper:=fun j=>upper Zero k h j-(v:ℝ)
  let D:=directions Zero ((carrier Zero k).observations.observations h) k h
  let row:=fun y:HeatCircle=>StoppedGaussianFeatures.stoppedRow σ target center ((q:ℝ)-(v:ℝ),y)
  let K:=timeWeight Zero ellOld (uniformConstant 1) k h*
    OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
      (carrier_orderedTimes Zero hages k h hp) center
  have hK:0≤K:=mul_nonneg
    (timeWeight_nonneg Zero hellOld (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k h hp)
    (OrderedHeatForests.parentDensity_nonneg 2 (by norm_num) k _ _ _)
  have hqv:(v:ℝ)≤(q:ℝ):=by exact_mod_cast hvq
  have hq0:0≤(q:ℝ)-(v:ℝ):=sub_nonneg.mpr hqv
  have hspanq:(q:ℝ)-(v:ℝ)≤1:=by
    have hqb: (q:ℝ)≤(b:ℝ):=hqt.le.trans (terminal_le_initial Zero k h)
    linarith [P.horizon_le_one]
  have hsig(i):0<σ i:=RelativeHistoryGeometry.relative_stop_pos Zero k h hqv hqt i
  have hsig1(i):σ i≤1:=(RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k h i).trans
    (hspan.trans P.horizon_le_one)
  have hage(i):σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hgap(i):(q:ℝ)-(v:ℝ)<target i:=sub_lt_sub_right (carrier_targets_after Zero h hages hqt i) _
  have hlo(j):(q:ℝ)-(v:ℝ)≤lo j:=sub_le_sub_right (hqt.le.trans (terminal_le_lower Zero k h j)) _
  have hint(j):lo j<upper j:=sub_lt_sub_right (lower_lt_upper Zero k h hp j) _
  have hstops(j i):σ i≤lo j ∨ upper j≤σ i:=RelativeHistoryGeometry.relative_stop_dichotomy Zero k h j i
  have hdisjoint(j l)(hne:j≠l):upper j≤lo l ∨ upper l≤lo j:=RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hn(j):σ (leafIndex k (fun i=>i) j)=target (leafIndex k (fun i=>i) j):=
    congrArg (fun z:ℝ=>z-v) (RelativeHistoryGeometry.native_leaf Zero k h hp j)
  have ht(j):target (leafIndex k (fun i=>i) j)∈Ioc 0 P.horizon:=
    RelativeHistoryGeometry.native_leaf_relative_age Zero (b:ℝ) P.horizon (fun _=>le_rfl) hspan k h hp hqv hqt j
  have hmatrix(a:Inputs):=ControlledThetaRelativeArrays.old_covariance_relative_fixed
    P haP Λ v b hvb Z htarget hstop F hF hFm (0,a) k h hqv hqt.le
  have hD(ω:Ω)(j:Fin k):D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j)).range:=by
    have hh:=(hforest (U ω,Dir ω)).1 j
    rw [hmatrix (U ω,Dir ω)] at hh
    exact hh
  have hold(ω:Ω):|∏j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j)|≤K:=by
    have hh:=(hforest (U ω,Dir ω)).2 hp hsmall
    change (∏j,scoreVariance (covariances Zero ((carrier Zero k).observations.observations h)
      (oldProfile P Λ v (U ω,Dir ω)) k h j) (D j))≤K at hh
    rw [hmatrix (U ω,Dir ω)] at hh
    have hnon:0≤∏j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ (U ω) (Dir ω)) lo upper j) (D j):=by
      apply Finset.prod_nonneg
      intro j _
      apply scoreVariance_nonneg _ (hD ω j)
      exact OldIntervalCovariance.covariance_posSemidef σ target center hage _
        (referenceProfile_measurable P Λ (U ω) (Dir ω))
        (fun p=>⟨((mul_pos (fraction_pos P) P.lower_pos).le.trans
          (referenceProfile_bounds P Λ (U ω) (Dir ω) p).1),
            (referenceProfile_bounds P Λ (U ω) (Dir ω) p).2⟩) (lo j) (upper j)
    rw [abs_of_nonneg hnon]
    exact hh
  let B:=fun ω=>ControlledFixedReserve.covariance P Λ (U ω) (Dir ω)
    (fixedProfile P Λ (U ω) (Dir ω) lo upper) σ target center ((q:ℝ)-(v:ℝ)) θ
  let coeff:=fun a:Ω×ℝ=>ControlledFixedReserve.coefficient P Λ (U a.1) (Dir a.1)
    (fixedProfile P Λ (U a.1) (Dir a.1) lo upper) a.2
  have hcm(a:Ω×ℝ):Measurable (coeff a):=
    ((ControlledProfile.profile_measurable P Λ (U a.1) (Dir a.1)).comp
      (measurable_const.prodMk measurable_id)).sub (fixedProfile_measurable P Λ (U a.1) (Dir a.1) lo upper)
  have hcB(a:Ω×ℝ)(p:StoppedGaussianFeatures.Domain):P.lower/2≤coeff a p ∧ coeff a p≤P.upper:=
    residual_bounds P Λ (U a.1) (Dir a.1) lo upper hdisjoint a.2 p
  have hfront(i):(carrier Zero k).terminal h-(v:ℝ)≤σ i:=sub_le_sub_right
    (le_min ((carrier Zero k).stops_after h i) (terminal_le_initial Zero k h)) _
  obtain ⟨hVi,hVm,hVdata⟩:=AllProfileInstantScoreMass.all_profiles σ target center hage hq0
    (sub_lt_sub_right hqt (v:ℝ)) hfront (half_pos P.lower_pos) coeff hcm hcB
  let V:=AllProfileInstantScoreMass.reference σ target center (P.lower/2) ((q:ℝ)-(v:ℝ))
  have hRange(ω:Ω):∀ᵐy:HeatCircle∂haarAddCircle,row y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (B ω)).range:=
    hVdata.mono (fun y hy=>(hy.2 (ω,θ)).1)
  have hB(ω:Ω):(B ω).PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target center hage _
    (hcm (ω,θ)) (fun p=>⟨(half_pos P.lower_pos).le.trans (hcB (ω,θ) p).1,(hcB (ω,θ) p).2⟩)
  have hEm(ω:Ω):Measurable (fun y:HeatCircle=>|e (ω,y)| *scoreVariance (B ω) (row y)):=
    (continuous_abs.measurable.comp (he.comp (measurable_const.prodMk measurable_id))).mul
      (scoreVariance_measurable.comp (measurable_const.prodMk
        ((StoppedGaussianFeatures.stoppedRow_measurable σ target center).comp (measurable_const.prodMk measurable_id))))
  have hEb(ω:Ω):∀ᵐy:HeatCircle∂haarAddCircle,
      ‖|e (ω,y)| *scoreVariance (B ω) (row y)‖≤ε*V y:=by
    filter_upwards [hVdata] with y hy
    have hv:0≤scoreVariance (B ω) (row y):=(hy.2 (ω,θ)).2.1
    rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg hv]
    exact mul_le_mul (hecap (ω,y)) (hy.2 (ω,θ)).2.2 hv hε
  have hEnergy(ω:Ω):Integrable (fun y:HeatCircle=>|e (ω,y)| *scoreVariance (B ω) (row y)) haarAddCircle:=
    (hVi.const_mul ε).mono' (hEm ω).aestronglyMeasurable (hEb ω)
  have hMass(ω:Ω):(∫y:HeatCircle,|e (ω,y)| *scoreVariance (B ω) (row y) ∂haarAddCircle)≤
      ε*((1+k:ℕ):ℝ)/((P.lower/2)*((carrier Zero k).terminal h-q)):=by
    have hh:=integral_mono_ae (hEnergy ω) (hVi.const_mul ε)
      ((hEb ω).mono (fun y hy=>(le_abs_self _).trans hy))
    rw [integral_const_mul] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hVm hε).trans_eq (by
      dsimp only [V]
      rw [sub_sub_sub_cancel_right]
      ring))
  have hMom:=MixedPastBoundedCovarianceInput.input_moment 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ haarAddCircle P hlocal hΛ hθ v q hvq hqH hspanq σ target center
    hsig hsig1 hage hgap lo upper hlo hint hstops hdisjoint D hD row
    ((StoppedGaussianFeatures.stoppedRow_measurable σ target center).comp (measurable_const.prodMk measurable_id))
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) hn ht (F (rootParameter k h))
    ((hF.smooth _).continuous.measurable) hA0 hν ((hF.smooth _).of_le (by simp)) hjet
    1 (by decide) B0 (by simpa using hBDG) e he K
      (ε*((1+k:ℕ):ℝ)/((P.lower/2)*((carrier Zero k).terminal h-q))) hK
      (div_nonneg (mul_nonneg hε (Nat.cast_nonneg _))
        (mul_nonneg (half_pos P.lower_pos).le (sub_pos.mpr hqt).le))
      hB hRange hEnergy hMass hold
  have hpoint(ω:Ω):value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q h e ω=
      (1/2:ℝ)*∫y:HeatCircle,e (ω,y)*PointwiseCompleteGaussianWord.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
        σ target center lo upper (Mean k θ q ω h) true D (row y)
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)) ∂haarAddCircle:=by
    unfold value
    apply congrArg (fun z:ℝ=>(1/2:ℝ)*z)
    apply integral_congr_ae
    filter_upwards [hVdata] with y hy
    let a:ℝ×Inputs:=(θ,(U ω,Dir ω))
    have hobs:=ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h
    have hterm:=ControlledReferenceThetaGeometry.carrier_terminal_eq
      P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm a (0,(0,0)) k h
    let Q:Fin (1+k)→Observation:=fun i=>⟨σ i,target i,center i⟩
    have hshift:ObservationTimeShift.observations (v:ℝ) Q=((carrier Zero k).observations.observations h):=by
      funext i
      change (⟨stops Zero k h i-v+v,targets Zero k h i-v+v,center i⟩:Observation)=_
      simp only [sub_add_cancel]
      unfold stops targets center centers
      rw [min_eq_left (CarrierStopBounds.stop_le_initial Zero hrootStop k h i)]
    have hrow:heatRow ((carrier (Base a) k).observations.observations h) q y=row y:=by
      rw [hobs,←hshift,show (q:ℝ)=((q:ℝ)-(v:ℝ))+(v:ℝ) by ring,
        ObservationTimeShift.heatRow_translation]
      ext i
      simp only [row,StoppedGaussianFeatures.stoppedRow,heatRow,Q,
        ite_eq_left ((sub_lt_sub_right hqt (v:ℝ)).trans_le (hfront i))]
    have hd:= (hy.2 (ω,θ)).1
    have hresω:=hres a q q.2 hqt.le
    change row y∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (B ω)).range at hd
    change fullResidualCovariance (Base a) (oldProfile P Λ v a.2) k h q=B ω at hresω
    rw [←hresω] at hd
    rw [hrow]
    exact congrArg (fun z:ℝ=>e (ω,y)*z) (hrep a q hqv (by simpa only [hterm] using hqt)
      (row y) (Mean k θ q ω h) hd)
  have heq:(fun ω=>|value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q h e ω|^2)=
      (fun ω=>|(1/2:ℝ)*∫y:HeatCircle,e (ω,y)*PointwiseCompleteGaussianWord.value P Λ (U ω) (Dir ω) θ ((q:ℝ)-(v:ℝ))
        σ target center lo upper (Mean k θ q ω h) true D (row y)
          (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)) ∂haarAddCircle|^2):=
    funext (fun ω=>congrArg (fun z:ℝ=>|z|^2) (hpoint ω))
  dsimp only
  rw [heq]
  convert! hMom using 1 <;> simp only [K,ellOld,σ,target,center,lo,upper,D,
    MixedPastLiteralPoint.meanField,show 2*1=2 by rfl,show 1*(k+2)=k+2 by omega]

end SHE.MixedPastNewestError
