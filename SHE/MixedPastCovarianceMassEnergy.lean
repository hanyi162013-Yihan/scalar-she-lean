module

public import SHE.MixedPastCovarianceSpatialFields
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

namespace SHE.MixedPastCovarianceMassEnergy
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastCovarianceMassEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastCovarianceMassEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastCovarianceMassEnergy_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastCovarianceMassEnergy_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastCovarianceMassEnergy_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastCovarianceMassEnergy_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
local instance mixedPastCovarianceMassEnergy_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastCovarianceMassEnergy_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastCovarianceMassEnergy_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
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

local notation "Mass" => MixedPastCovarianceSpatialFields.scoreMass 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm

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
      let C:=ControlledProfile.sharpUnit P*(((1+k:ℕ):ℝ)/(P.lower/2)*
        (((carrier Zero k).terminal (anchor k t)-(q:ℝ))/2)^((P.exponent-1)/4)*
          (1+2/(((P.exponent-1)/4)+1)))
      Integrable (fun z : Ω×HeatCircle=>|Mass k θ q t (z,w)|^2) (μ.prod haarAddCircle) ∧
        (∫ z : Ω×HeatCircle,|Mass k θ q t (z,w)|^2 ∂μ.prod haarAddCircle)≤
          C^2*(∫ ω,‖S.second v ω-S.first v ω‖^2 ∂μ) := by
  filter_upwards [MixedPastScoreEnergy.actual_score_mass_energy
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
  simpa only [MixedPastCovarianceSpatialFields.scoreMass,he,C,a,σ,target,lo,hi] using hh

end SHE.MixedPastCovarianceMassEnergy
