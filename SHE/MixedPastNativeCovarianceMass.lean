module

public import SHE.MixedPastCovariancePointMoments
public import SHE.MixedPastNativeScoreEnergy
public import SHE.NativePastAgeScoreEnergy
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

namespace SHE.MixedPastNativeCovarianceMass
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceSpatialFields_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceSpatialFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceSpatialFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceSpatialFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
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
local instance mixedPastCovarianceSpatialFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceSpatialFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceSpatialFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

/-- Literal physical random score mass in relative coordinates. -/
def scoreMass (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ)
    (z : (Ω×HeatCircle)×(Fin k→HeatCircle)) : ℝ :=
  let a:=anchor k t
  let σ:=fun i=>stops Zero k a i-(v:ℝ)
  let target:=fun i=>targets Zero k a i-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  let cen:=fun i=>values (fun _ : Fin 1=>(0:HeatCircle)) k z.2 i+z.1.2
  ∫ p,|ControlledProfile.derivative P Λ (U z.1.1) (Dir z.1.1) (p,θ)| *scoreVariance
    (ControlledFixedReserve.covariance P Λ (U z.1.1) (Dir z.1.1)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (U z.1.1) (Dir z.1.1) lo hi)) σ target cen ((q:ℝ)-(v:ℝ)) θ)
    (StoppedGaussianFeatures.stoppedRow σ target cen p)
      ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))

local notation "Mass" => scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

/-- The true continuum score mass is jointly Borel even when all old
relative locations, output root and the past profile vary together. -/
theorem scoreMass_measurable (hΛ : 0≤Λ)
    (hsmall : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (k : ℕ) (θ : ℝ) (q : ℝ≥0) (t : Fin k→ℝ) : Measurable (Mass k θ q t) := by
  let a:=anchor k t
  let σ:=fun i=>stops Zero k a i-(v:ℝ)
  let target:=fun i=>targets Zero k a i-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  let u : (Ω×(Fin k→HeatCircle))→CircleL2:=fun z=>U z.1
  let d : (Ω×(Fin k→HeatCircle))→CircleL2:=fun z=>Dir z.1
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hu : Measurable u:=hU.comp measurable_fst
  have hd : Measurable d:=hDir.comp measurable_fst
  let c : (Ω×(Fin k→HeatCircle))×ControlledProfile.Domain→ℝ:=fun z=>
    ControlledProfile.profile P Λ (u z.1) (d z.1) (θ,z.2)-NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u z.1) (d z.1) lo hi) z.2
  let e : (Ω×(Fin k→HeatCircle))×ControlledProfile.Domain→ℝ:=fun z=>
    ControlledProfile.derivative P Λ (u z.1) (d z.1) (z.2,θ)
  have hc : Measurable c := (VaryingControlledGaussianFields.profile_measurable P Λ θ u d hu hd).sub
    ((VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d hu hd lo hi).add_const _)
  have he : Measurable e := by
    have hmap : Measurable (fun z : (Ω×(Fin k→HeatCircle))×ControlledProfile.Domain=>(z,θ)) :=
      measurable_id.prodMk measurable_const
    convert! (ControlledProfile.random_derivative_measurable P hΛ u d hu hd hsmall).comp hmap using 1
  let center : (Ω×(Fin k→HeatCircle))→Fin (1+k)→HeatCircle:=fun z=>values (fun _ : Fin 1=>(0:HeatCircle)) k z.2
  have hcenter : Measurable center := (values_continuous (fun _ : Fin 1=>(0:HeatCircle)) k).measurable.comp measurable_snd
  have hh:=futureInput_random_centers_measurable σ target center hcenter c e hc he ((q:ℝ)-(v:ℝ))
  have hmap : Measurable (fun z : (Ω×HeatCircle)×(Fin k→HeatCircle)=>((z.1.1,z.2),z.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  convert! hh.comp hmap using 1


include hIJ₀ hIJ₁ in
/-- Sharp actual random-past covariance score mass, in the original
relative old-space coordinates. A single theta event covers EVERY old
location and time section, so no random substitution into exceptional
sets is made. -/
theorem actual_mass_energy (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ) (q : ℝ≥0) (hvq : v≤q) :
    ∀ᵐ θ ∂volume,∀ t : Fin k→ℝ,active Zero (b:ℝ) k q t→
      ∀ w : Fin k→HeatCircle,
      let C:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(3*P.lower/8)*
        (((carrier Zero k).terminal (anchor k t)-(q:ℝ))/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun z : Ω×HeatCircle=>|Mass k θ q t (z,w)|^2) (μ.prod haarAddCircle) ∧
        (∫ z : Ω×HeatCircle,|Mass k θ q t (z,w)|^2 ∂μ.prod haarAddCircle)≤
          C^2*(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  filter_upwards [MixedPastNativeScoreEnergy.actual_score_mass_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ v
    P hΛ hsmallPoint hsmallL2 hvH hv1 Bpast hBDGpast] with θ hθ
  intro t hactive w C
  let a:=anchor k t
  let σ:=fun i=>stops Zero k a i-(v:ℝ)
  let target:=fun i=>targets Zero k a i-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  have hqv : (v:ℝ)≤(q:ℝ) := by exact_mod_cast hvq
  have hq0 : 0≤(q:ℝ)-(v:ℝ) := sub_nonneg.mpr hqv
  have ht : (q:ℝ)<(carrier Zero k).terminal a := by
    have he:=terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    change (carrier Zero k).terminal a=fixedTerminal (R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t at he
    exact he.symm ▸ hactive.2
  have hdj (j l) (hne:j≠l) : hi j≤lo l ∨ hi l≤lo j :=
    RelativeHistoryGeometry.relative_disjoint Zero k a j l hne
  have hsig1 (i) : σ i-((q:ℝ)-(v:ℝ))≤1 := by
    have hs := (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k a i).trans
      (hspan.trans P.horizon_le_one)
    change stops Zero k a i-(v:ℝ)≤1 at hs
    change stops Zero k a i-(v:ℝ)-((q:ℝ)-(v:ℝ))≤1
    linarith
  have hage (i) : σ i≤target i := sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k a i)) _
  have hqa : (q:ℝ)-(v:ℝ)<(carrier Zero k).terminal a-(v:ℝ) := sub_lt_sub_right ht _
  have hstops (i) : (carrier Zero k).terminal a-(v:ℝ)≤σ i := sub_le_sub_right
    (le_min ((carrier Zero k).stops_after a i) (terminal_le_initial Zero k a)) _
  have hh:=hθ ((q:ℝ)-(v:ℝ)) hq0 k lo hi hdj (1+k) σ target
    (values (fun _ : Fin 1=>(0:HeatCircle)) k w) hsig1 hage
      ((carrier Zero k).terminal a-(v:ℝ)) hqa hstops
  have he : ((carrier Zero k).terminal a-(v:ℝ))-((q:ℝ)-(v:ℝ))=
      (carrier Zero k).terminal a-(q:ℝ) := by ring
  simpa only [MixedPastNativeCovarianceMass.scoreMass,he,C,a,σ,target,lo,hi] using hh


include hIJ₀ hIJ₁ in
/-- Sharp actual random-past covariance score mass, in the original
relative old-space coordinates. A single theta event covers EVERY old
location and time section, so no random substitution into exceptional
sets is made. -/
theorem actual_past_mass_energy (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1)
    (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (k : ℕ) (q : ℝ≥0) (hvq : v<q) :
    ∀ᵐ θ ∂volume,∀ t : Fin k→ℝ,active Zero (b:ℝ) k q t→
      ∀ w : Fin k→HeatCircle,
      let C:=(ControlledProfile.sharpUnit P*((q:ℝ)-(v:ℝ))^((P.exponent-1)/4))*
        ((((1+k:ℕ):ℝ)/(3*P.lower/8))*3)
      Integrable (fun z : Ω×HeatCircle=>|Mass k θ q t (z,w)|^2) (μ.prod haarAddCircle) ∧
        (∫ z : Ω×HeatCircle,|Mass k θ q t (z,w)|^2 ∂μ.prod haarAddCircle)≤
          C^2*(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDenergy:=MixedHeatedDifferenceMoments.current_energy
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 1 (by decide) Bpast hBDGpast
  have hDi:Integrable (fun ω=>‖Dir ω‖^2) μ:=by
    simpa only [MixedPastJointData.pastD,NativeHeatObservation.embed_norm] using hDenergy.1
  filter_upwards [random_native_past_age_energy P hΛ U Dir hU hDir hsmallPoint hsmallL2 μ hDi] with θ hθ
  intro t hactive w C
  let a:=anchor k t
  let σ:=fun i=>stops Zero k a i-(v:ℝ)
  let target:=fun i=>targets Zero k a i-(v:ℝ)
  let lo:=fun j=>lower Zero k a j-(v:ℝ)
  let hi:=fun j=>upper Zero k a j-(v:ℝ)
  have hqv : (v:ℝ)≤(q:ℝ) := by exact_mod_cast hvq.le
  have hq0 : 0≤(q:ℝ)-(v:ℝ) := sub_nonneg.mpr hqv
  have ht : (q:ℝ)<(carrier Zero k).terminal a := by
    have he:=terminal_separated Zero (b:ℝ) (fun _=>rfl) k t (0:HeatCircle) (fun _=>0)
    change (carrier Zero k).terminal a=fixedTerminal (R:=referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) (b:ℝ) k t at he
    exact he.symm ▸ hactive.2
  have hdj (j l) (hne:j≠l) : hi j≤lo l ∨ hi l≤lo j :=
    RelativeHistoryGeometry.relative_disjoint Zero k a j l hne
  have hsig1 (i) : σ i-((q:ℝ)-(v:ℝ))≤1 := by
    have hs := (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k a i).trans
      (hspan.trans P.horizon_le_one)
    change stops Zero k a i-(v:ℝ)≤1 at hs
    change stops Zero k a i-(v:ℝ)-((q:ℝ)-(v:ℝ))≤1
    linarith
  have hage (i) : σ i≤target i := sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k a i)) _
  have hqa : (q:ℝ)-(v:ℝ)<(carrier Zero k).terminal a-(v:ℝ) := sub_lt_sub_right ht _
  have hstops (i) : (carrier Zero k).terminal a-(v:ℝ)≤σ i := sub_le_sub_right
    (le_min ((carrier Zero k).stops_after a i) (terminal_le_initial Zero k a)) _
  let old:Ω×ControlledProfile.Domain→ℝ:=fun z=>fixedProfile P Λ (U z.1) (Dir z.1) lo hi z.2
  have ho:Measurable old:=VaryingControlledGaussianFields.fixed_profile_measurable P Λ U Dir hU hDir lo hi
  have hob(z:Ω×ControlledProfile.Domain):0≤old z ∧ old z≤P.lower/2:=
    fixedProfile_bounds P Λ (U z.1) (Dir z.1) lo hi hdj z.2
  have hqpos:0<(q:ℝ)-(v:ℝ):=sub_pos.mpr (by exact_mod_cast hvq)
  have hh:=hθ ((q:ℝ)-(v:ℝ)) hqpos old ho hob (1+k) σ target
    (values (fun _ : Fin 1=>(0:HeatCircle)) k w) hsig1 hage
      ((carrier Zero k).terminal a-(v:ℝ)) hqa hstops
  convert! hh using 1 <;> simp only [MixedPastJointData.pastD,embed_norm] <;> rfl


end SHE.MixedPastNativeCovarianceMass
