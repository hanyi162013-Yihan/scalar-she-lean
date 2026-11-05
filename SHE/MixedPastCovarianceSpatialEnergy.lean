module

public import SHE.MixedPastCovarianceMassEnergy
public import SHE.RandomScoreSpatialAverage
public import SHE.HistoryRelativeOldFirst
public import SHE.ScalarRootSharpSections
public import SHE.MixedPastScoreEnergy
public import SHE.RandomFutureCenters
public import SHE.PastMeanSections
public import SHE.QuarterSpatialEvent
public import SHE.PastCovarianceMassSections

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastCovarianceSpatialEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastCovarianceSpatialEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open ScalarRootRelativeGeometry ControlledResidualScoreInput MeasurableGaussianScores
  ProfileStability QuarterSpatialEvent OrderedHeatForests
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

local notation "Point" => MixedPastCovarianceSpatialFields.relativePoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm
local notation "Mass" => MixedPastCovarianceSpatialFields.scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

include hIJ₀ hIJ₁ in
/-- The actual correlated random-past covariance leg, averaged in
original old space before taking sample/output energy. The actual past
solution difference is the only random energy on the right. -/
theorem actual_spatial_energy (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hcenter : ∀ x,(Z.observations x 0).center=x)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ) (q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) :
    ∀ᵐ θ ∂volume,|θ|≤1→∀ᵐ t : Fin k→ℝ
        ∂Measure.pi (fun _=>volume.restrict (Ioc (v:ℝ) (b:ℝ))),
      active Zero (b:ℝ) k q t→SmallHistory Zero (uniformHorizon 1) k (anchor k t)→
      ∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)→
      ∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let a:=anchor k t
      let CG:=MixedPastWordMoments.momentConstant P k k 1
        ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
      let scale:=timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k a*
        PastWordTimeFields.total Zero P k a A0 ν/2
      let gain:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(P.lower/2)*
        (((carrier Zero k).terminal a-(q:ℝ))/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1)))
      let E:=gain^2*(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ)
      Integrable (fun z : Ω×HeatCircle=>|∫ w,Point k θ q t (z,w)
        ∂Measure.pi (fun _ : Fin k=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫ z : Ω×HeatCircle,|∫ w,Point k θ q t (z,w)
        ∂Measure.pi (fun _ : Fin k=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
          (CG*scale^2)*E*(Fintype.card (Choices 1 k):ℝ)^2 := by
  have hagesZ : ∀ x i,((Zero).observations.observations x i).stop≤((Zero).observations.observations x i).target:=hages
  have hT : ∀ x,(Zero).terminal x=(b:ℝ):=fun _=>rfl
  have hA : ∀ x i,((Zero).observations.observations x i).target=(b:ℝ):=hrootTarget
  have hσ : ∀ x i,((Zero).observations.observations x i).stop=(b:ℝ):=fun x i=>le_antisymm (hrootStop x i) (hstop x i)
  have hc : ∀ x i,((Zero).observations.observations x i).center=x := by
    intro x i
    fin_cases i
    exact hcenter x
  have hpoint:=MixedPastCovariancePointMoments.actual_even_energy_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hsmallPoint hvH hv1 Bpast hBDGpast
      hages hspan haarAddCircle k
  have hsec:=ae_relative_old_first _ k hpoint
  have hmass:=MixedPastCovarianceMassEnergy.actual_mass_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁
    P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint hsmallL2 hvH hv1
      Bpast hBDGpast hages hspan k q hvq
  filter_upwards [hmass] with θ hθmass
  intro hθ
  filter_upwards [hsec] with t ht
  intro hactive hsmall A0 ν hA0 hν hjet B0 hBDG a CG scale gain E
  let p:=fun (x : HeatCircle) (w : Fin k→HeatCircle)=>separated k (x,t,fun i=>w i+x)
  let tt:=targets Zero k a
  have hord : OrderedTimes k tt:=carrier_orderedTimes Zero hagesZ k a hactive.1
  let K : (Fin k→HeatCircle)→ℝ:=fun w=>parentDensity 2 (by norm_num) k tt hord
    (values (fun _ : Fin 1=>(0:HeatCircle)) k w)
  have hKm : Continuous K:=(parentDensity_continuous 2 (by norm_num) k tt hord).comp
    (values_continuous (fun _ : Fin 1=>(0:HeatCircle)) k)
  have hKi : Integrable K (Measure.pi (fun _ : Fin k=>haarAddCircle)):=
    hKm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKn (w) : 0≤K w:=parentDensity_nonneg 2 (by norm_num) k tt hord _
  have hp' (x w) : StrictHistory Zero k (p x w):=
    (FixedHistoryTimeFactors.strict_sections Zero (b:ℝ) hT k t x 0 _ _).mpr hactive.1
  have hs' (x w) : SmallHistory Zero (uniformHorizon 1) k (p x w):=
    (small_history_sections Zero (b:ℝ) hT (b:ℝ) hA (uniformHorizon 1) k t x 0 _ _).mpr hsmall
  have hqt (x w) : (q:ℝ)<(carrier Zero k).terminal (p x w):=by
    simpa only [p,terminal_separated Zero (b:ℝ) hT] using hactive.2
  have hmEq (x w ω) :
      (∫ r,|MixedPastLiteralCovariance.direction 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v θ (ω,r)| *scoreVariance
        (ControlledFixedReserve.covariance P Λ (U ω) (Dir ω)
          (fixedProfile P Λ (U ω) (Dir ω) (fun j=>lower Zero k (p x w) j-(v:ℝ)) (fun j=>upper Zero k (p x w) j-(v:ℝ)))
          (fun i=>stops Zero k (p x w) i-(v:ℝ)) (fun i=>targets Zero k (p x w) i-(v:ℝ)) (centers Zero k (p x w)) ((q:ℝ)-(v:ℝ)) θ)
        (StoppedGaussianFeatures.stoppedRow (fun i=>stops Zero k (p x w) i-(v:ℝ)) (fun i=>targets Zero k (p x w) i-(v:ℝ)) (centers Zero k (p x w)) r)
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ)))=Mass k θ q t ((ω,x),w) := by
    have hl:=FixedHistoryTimeFactors.lower_sections Zero (b:ℝ) hT k t x 0 (fun i=>w i+x) (fun _=>0)
    have hu:=FixedHistoryTimeFactors.upper_sections Zero (b:ℝ) hT k t x 0 (fun i=>w i+x) (fun _=>0)
    have hta:=FixedHistoryTimeFactors.targets_sections Zero (b:ℝ) hT (fun _=>(b:ℝ)) hA k t x 0 (fun i=>w i+x) (fun _=>0)
    have hst:=covered_stops_sections Zero (b:ℝ) hT (b:ℝ) hσ k t x 0 (fun i=>w i+x) (fun _=>0)
    simp only [p,hl,hu,hta,hst,centers_relative Zero hc,
      MixedPastLiteralCovariance.direction,MixedPastCovarianceSpatialFields.scoreMass]
    rfl
  have hmEqSep:=hmEq
  dsimp only [p] at hmEqSep
  have hb : ∀ᵐ w : Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),∀ᵐ x : HeatCircle ∂haarAddCircle,
      Integrable (fun ω=>|Mass k θ q t ((ω,x),w)|^2) μ→
      Integrable (fun ω=>|Point k θ q t ((ω,x),w)|^2) μ ∧
      (∫ ω,|Point k θ q t ((ω,x),w)|^2 ∂μ)≤(CG*scale^2)*(K w)^2*
        (∫ ω,|Mass k θ q t ((ω,x),w)|^2 ∂μ) := by
    filter_upwards [ht] with w hw
    filter_upwards [hw] with x hx
    intro hmi
    have hh:=hx q hvq hqH (hqt x w) (hp' x w) (hs' x w) θ hθ A0 ν hA0 hν
      (fun j hj z=>by simpa only [root_separated] using hjet x j hj z) B0 hBDG
    have hwgt:=FixedHistoryTimeFactors.timeWeight_sections Zero (b:ℝ) hT (fraction P*P.lower) (uniformConstant 1)
      k t x 0 (fun i=>w i+x) (fun _=>0)
    have htot:=PastWordTimeFields.total_sections Zero P (b:ℝ) hT (fun _=>(b:ℝ)) hA
      k t x 0 (fun i=>w i+x) (fun _=>0) A0 ν
    have hpar:=parent_density_relative Zero (b:ℝ) hT 2 (by norm_num) (b:ℝ) hA hc k t x w
      (carrier_orderedTimes Zero hagesZ k (p x w) (hp' x w))
    dsimp only at hh
    simp only [hmEqSep] at hh
    change Integrable (fun ω=>|Actual k θ q (ω,p x w)|^2) μ ∧
      (∫ ω,|Actual k θ q (ω,p x w)|^2 ∂μ)≤CG*
        ((timeWeight Zero (fraction P*P.lower) (uniformConstant 1) k (p x w)*
          parentDensity 2 (by norm_num) k (targets Zero k (p x w))
            (carrier_orderedTimes Zero hagesZ k (p x w) (hp' x w)) (centers Zero k (p x w)))*
          PastWordTimeFields.total Zero P k (p x w) A0 ν/2)^2*
            (∫ ω,(Mass k θ q t ((ω,x),w))^2 ∂μ) at hh
    change PastWordTimeFields.total Zero P k (p x w) A0 ν=_ at htot
    rw [hpar,hwgt,htot] at hh
    refine ⟨hh.1,?_⟩
    convert! hh.2 using 1 <;> dsimp only [CG,scale,K,tt,MixedPastCovarianceSpatialFields.relativePoint,p,a,anchor] <;> simp only [sq_abs] <;> ring
  have hf:=MixedPastCovarianceSpatialFields.relativePoint_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q t
  have hm:=MixedPastCovarianceSpatialFields.scoreMass_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm hΛ hsmallPoint k θ q t
  have hh:=RandomScoreSpatialAverage.average_energy μ haarAddCircle (Measure.pi (fun _ : Fin k=>haarAddCircle))
    (Point k θ q t) (Mass k θ q t) hf hm K hKm.measurable hKi hKn
      (mul_nonneg (MixedPastWordMoments.momentConstant_nonneg _ _ _ _ _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg gain) (integral_nonneg (fun _=>sq_nonneg _)))
      (ae_of_all _ (fun w=>hθmass t hactive w)) hb
  rw [parentDensity_mass 2 (by norm_num) k tt hord (fun _ : Fin 1=>(0:HeatCircle))] at hh
  exact hh

end SHE.MixedPastCovarianceSpatialEnergy
