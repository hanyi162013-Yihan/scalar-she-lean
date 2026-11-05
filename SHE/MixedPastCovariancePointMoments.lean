module

public import SHE.MixedPastCovarianceFields
public import SHE.RandomFutureInputPoint
public import SHE.MixedHilbertInputMoments
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedPastCovariancePointMoments
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovariancePointMoments_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovariancePointMoments_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovariancePointMoments_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovariancePointMoments_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovariancePointMoments_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovariancePointMoments_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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


local instance mixedPastCovariancePointMoments_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovariancePointMoments_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {n : ℕ}



open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  ControlledFamilyProfileForest GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance mixedPastCovariancePointMoments_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Edir" => MixedPastLiteralCovariance.direction 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v
local notation "Actual" => MixedPastLiteralCovariance.actualPoint 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm
open ControlledResidualScoreInput ProfileStability ProfileL2

include hIJ₀ hIJ₁ in
/-- The complete literal covariance point with its ACTUAL profile
input. Every signed-input Bochner and sample-moment applicability
condition is now discharged by the actual pair. Its true random score
mass remains inside expectation for the sharp spatial transfer. -/
theorem actual_even_energy_ae (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hvH : v≤H) (hv1 : (v:ℝ)≤1) (Bpast : ℝ≥0) (hBDGpast : StandardTerminalBDGPower 1 J Bpast)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) ρ k,
      ∀ q : ℝ≥0,v≤q→q≤H→(q:ℝ)<(carrier Zero k).terminal h→
      ∀ hp : StrictHistory Zero k h,SmallHistory Zero (uniformHorizon n) k h→
      ∀ θ : ℝ,|θ|≤1→∀ A0 ν : ℝ,0≤A0→0≤ν→
      (∀ j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      ∀ B0 : ℝ≥0,StandardTerminalBDGPower (k+2) J B0→
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let B:=fun ω=>ControlledFixedReserve.covariance P Λ (U ω) (Dir ω)
        (fixedProfile P Λ (U ω) (Dir ω) lo hi) σ target (centers Zero k h) ((q:ℝ)-(v:ℝ)) θ
      let mass:=fun ω=>∫ x,|Edir θ (ω,x)| *scoreVariance (B ω)
        (StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) x)
          ∂StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))
      let oldEnvelope:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k (targets Zero k h)
          (carrier_orderedTimes Zero hages k h hp) (centers Zero k h)
      let sharp:=MixedPastWordMoments.total (d:=n) P lo hi
        (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
      Integrable (fun ω=>|Actual k θ q (ω,h)|^2) μ ∧
        (∫ ω,|Actual k θ q (ω,h)|^2 ∂μ)≤
          MixedPastWordMoments.momentConstant P k k 1
            ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)*
              (oldEnvelope*sharp/2)^2*(∫ ω,(mass ω)^2 ∂μ) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hD := MixedHeatedDifferenceMoments.current_energy 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ S J hIJ₀ hIJ₁ hΛ v hvH hv1 1 (by decide) Bpast hBDGpast
  have hDi : Integrable (fun ω=>‖Dir ω‖^2) μ := by simpa only [MixedPastJointData.pastD,embed_norm] using hD.1
  filter_upwards [MixedPastLiteralCovariance.even_moment_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm
      hlocal hΛ hages hspan ρ k] with h hh
  intro q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet B0 hBDG σ target lo hi B mass oldEnvelope sharp
  let old : Ω×ControlledProfile.Domain→ℝ := fun z=>fixedProfile P Λ (U z.1) (Dir z.1) lo hi z.2
  have ho : Measurable old := VaryingControlledGaussianFields.fixed_profile_measurable P Λ U Dir hU hDir lo hi
  have hdj (j l) (hne:j≠l) : hi j≤lo l ∨ hi l≤lo j := RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hob (z : Ω×ControlledProfile.Domain) : 0≤old z ∧ old z≤P.lower/2 :=
    fixedProfile_bounds P Λ (U z.1) (Dir z.1) lo hi hdj z.2
  have hqv : (v:ℝ)≤(q:ℝ) := by exact_mod_cast hvq
  have hq0 : 0≤(q:ℝ)-(v:ℝ) := sub_nonneg.mpr hqv
  have hsig1 (i) : σ i-((q:ℝ)-(v:ℝ))≤1 := by
    have hs := (RelativeHistoryGeometry.relative_stop_le_span Zero (b:ℝ) (fun _=>le_rfl) k h i).trans
      (hspan.trans P.horizon_le_one)
    change stops Zero k h i-(v:ℝ)≤1 at hs
    change stops Zero k h i-(v:ℝ)-((q:ℝ)-(v:ℝ))≤1
    linarith
  have hage (i) : σ i≤target i := sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  let a : ℝ := (carrier Zero k).terminal h-(v:ℝ)
  have hqa : (q:ℝ)-(v:ℝ)<a := sub_lt_sub_right hqt _
  have hstops (i) : a≤σ i := sub_le_sub_right
    (le_min ((carrier Zero k).stops_after h i) (terminal_le_initial Zero k h)) _
  have hcoeff (ω : Ω) : ControlledFixedReserve.coefficient P Λ (U ω) (Dir ω)
      (fixedProfile P Λ (U ω) (Dir ω) lo hi) θ=
        (fun p=>profile P Λ (U ω) (Dir ω) (θ,p)-old (ω,p)) := by funext p; rfl
  have hEnergy (ω : Ω) : Integrable (fun x=>|Edir θ (ω,x)| *scoreVariance (B ω)
      (StoppedGaussianFeatures.stoppedRow σ target (centers Zero k h) x))
        (StoppedGaussianFeatures.historyMeasure ((q:ℝ)-(v:ℝ))) := by
    have hh := future_input_integrable P hΛ (U ω) (Dir ω) hsmallPoint θ ((q:ℝ)-(v:ℝ)) hq0
      (fun p=>old (ω,p)) (ho.comp (measurable_const.prodMk measurable_id)) (fun p=>hob (ω,p))
      (n+k) σ target (centers Zero k h) hsig1 hage a hqa hstops (0:HeatCircle)
    simp only [B,ControlledFixedReserve.covariance,hcoeff]
    simpa only [MixedPastLiteralCovariance.direction,add_zero] using hh
  have hMassI : Integrable (fun ω=>(mass ω)^2) μ := by
    have hh := random_future_point_integrable P hΛ U Dir hU hDir hsmallPoint μ hDi
      θ ((q:ℝ)-(v:ℝ)) hq0 old ho hob (n+k) σ target (centers Zero k h) hsig1 hage a hqa hstops (0:HeatCircle)
    simp only [mass,B,ControlledFixedReserve.covariance,hcoeff]
    simpa only [MixedPastLiteralCovariance.direction,futureInput,add_zero] using hh
  have hep := MixedPastLiteralCovariance.direction_past_measurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P v hΛ hsmallPoint θ
  have he : Measurable (Edir θ) := by
    have hmap : Measurable (fun z : Ω×ControlledProfile.Domain=>(z,θ)) := measurable_id.prodMk measurable_const
    convert! (ControlledProfile.random_derivative_measurable P hΛ U Dir hU hDir hsmallPoint).comp hmap using 1
  have hfinal := hh q hvq hqH hqt hp hsmall θ hθ A0 ν hA0 hν hjet
    1 (by decide) B0 (by simpa only [one_mul] using hBDG) (Edir θ) he hep hEnergy
      (by simpa only [mul_one] using hMassI)
  simpa only [MixedPastLiteralCovariance.actualPoint,mul_one,one_mul] using hfinal

end SHE.MixedPastCovariancePointMoments
