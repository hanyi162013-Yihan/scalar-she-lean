module

public import SHE.MovingMeanOldAverage
public import SHE.CanonicalPastMeanInput

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanCanonical
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanCanonical_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanCanonical_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanCanonical_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanCanonical_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanCanonical_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanCanonical_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanCanonical_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanCanonical_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanCanonical_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanCanonical_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P P.coefficient haP Λ h Z htarget hstop F hF hFm
local notation "ZT" v=>ObservationFamilyTimeShift.family (v:ℝ) Z
local notation "HT" v=>ControlledWordTimeShift.translatedTargets h Z htarget v
local notation "HS" v=>ControlledWordTimeShift.translatedStops h Z hstop v

/-- The translated canonical Hilbert mean input is the actual
conditional-law native input used by the sharp random-past estimate. -/
theorem absoluteAt_eq_input
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v s : ℝ≥0) (θ : ℝ) (t : Fin k→ℝ) (ω : Ω) :
    AA k mass ρ hmass hρ v
      (embed (S.first v ω),embed (S.second v ω-S.first v ω)) s
      (embed (S.first (v+s) ω)) (embed (S.second (v+s) ω-S.first (v+s) ω)) θ t
      (S.second (v+s) ω-S.first (v+s) ω)=
    MixedPastMeanInputEnergy.input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
      k θ (v+s) mass ρ hmass hρ t ω := by
  have hages' : ∀ x i,((ZT v).observations x i).stop≤((ZT v).observations x i).target := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤(Z.observations x i).target+(v:ℝ)
    linarith [hages x i]
  have hroot' : ∀ x i,((ZT v).observations x i).stop≤((v+h:ℝ≥0):ℝ) := by
    intro x i
    change (Z.observations x i).stop+(v:ℝ)≤((v+h:ℝ≥0):ℝ)
    rw [NNReal.coe_add]
    linarith [hrootStop x i]
  rw [←CanonicalPastMeanInput.canonicalInput_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm
    hages' hroot' k θ (v+s) mass ρ hmass hρ t ω]
  unfold ControlledMeanOldAverageShift.absoluteAt ControlledMeanInputShift.absoluteInput
    CanonicalPastMeanInput.canonicalInput ActualMeanKernel.familyMeanInput ControlledMeanTimeShift.absoluteMean
  have hq : (s:ℝ)+(v:ℝ)=((v+s:ℝ≥0):ℝ):=by simp only [NNReal.coe_add,add_comm]
  simp only [sub_add_cancel,hq]
  rfl

/-- This is the literal old-time averaged field, with no new field
additivity, conditional Gaussian law, or moving-profile premise. -/
theorem absoluteAverage_eq_average
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(h:ℝ))
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v s : ℝ≥0) (θ : ℝ) (ω : Ω) :
    MovingMeanOldAverage.absoluteAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P P.coefficient haP h Z htarget hstop F hF hFm k mass ρ hmass hρ
      (fun _ : Unit=>v) (fun _=>s) (fun _=>θ) (fun _=>ω) ()=
    MixedPastMeanFields.average 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
      P haP v (v+h) (show v≤v+h from le_self_add) (ZT v) (HT v) (HS v) F hF hFm k
      (Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (v:ℝ) ((v+h:ℝ≥0):ℝ))))
      θ (v+s) mass ρ hmass hρ ω := by
  unfold MovingMeanOldAverage.absoluteAverage MixedPastMeanFields.average
  simp only [NNReal.coe_add]
  apply integral_congr_ae
  filter_upwards [] with t
  exact absoluteAt_eq_input 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hages hrootStop k mass ρ hmass hρ v s θ t ω

end SHE.MovingMeanCanonical

