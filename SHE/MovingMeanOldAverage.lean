module

public import SHE.MovingNativeFields
public import SHE.ControlledMeanOldAverageShift

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanOldAverage
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanOldAverage_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanOldAverage_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanOldAverage_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanOldAverage_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanOldAverage_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanOldAverage_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingMeanOldAverage_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanOldAverage_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanOldAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanOldAverage_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]


open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "AR"=>ControlledMeanOldAverageShift.relativeAt P A hA Λ h Z htarget hstop F hF hFm
local notation "AA"=>ControlledMeanOldAverageShift.absoluteAt P A hA Λ h Z htarget hstop F hF hFm

/-- The actual moving-window old-time mean average, using every
original absolute old time before taking its Hilbert norm. -/
def absoluteAverage (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (past age : W→ℝ≥0) (θ : W→ℝ) (ω : W→Ω) (w : W) : CircleL2 :=
  ∫ t,AA k mass ρ hmass hρ (past w)
    (embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
    (age w) (embed (S.first (past w+age w) (ω w)))
    (embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))) (θ w) t
    (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))
    ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc (past w:ℝ) ((past w:ℝ)+(h:ℝ))))

/-- Its fixed-relative-cube realization is the same genuine Hilbert
field, not a separately chosen measurable modification. -/
theorem absoluteAverage_eq_relative (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (past age : W→ℝ≥0) (θ : W→ℝ) (ω : W→Ω) (w : W) :
    absoluteAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k mass ρ hmass hρ past age θ ω w=
    ∫ t,MovingNativeFields.relativeMeanInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k mass ρ hmass hρ
      (fun z : (Fin k→ℝ)×W=>past z.2) (fun z=>age z.2) (fun z=>θ z.2) Prod.fst
      (fun z=>ω z.2) (t,w) ∂Measure.pi (fun _ : Fin k=>volume.restrict (Ioc 0 (h:ℝ))) := by
  unfold absoluteAverage
  rw [ControlledMeanOldAverageShift.old_average_translation]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold MovingNativeFields.relativeMeanInput
  exact (ControlledMeanOldAverageShift.relative_section P A hA Λ h Z htarget hstop F hF hFm
    k mass ρ hmass hρ
    (fun z : (Fin k→ℝ)×W=>(embed (S.first (past z.2) (ω z.2)),
      embed (S.second (past z.2) (ω z.2)-S.first (past z.2) (ω z.2))))
    (fun z=>(age z.2:ℝ))
    (fun z=>embed (S.first (past z.2+age z.2) (ω z.2)))
    (fun z=>embed (S.second (past z.2+age z.2) (ω z.2)-S.first (past z.2+age z.2) (ω z.2)))
    (fun z=>θ z.2) Prod.fst
    (fun z=>S.second (past z.2+age z.2) (ω z.2)-S.first (past z.2+age z.2) (ω z.2)) (t,w)).symm

/-- True joint moving-past/current/theta Borel measurability after
the entire original old-time cube has been averaged before squaring. -/
theorem absoluteAverage_measurable (hΛ : 0≤Λ) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (θ : W→ℝ) (hθ : Measurable θ) (ω : W→Ω) (hω : Measurable ω) :
    Measurable (absoluteAverage 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k mass ρ hmass hρ past age θ ω) := by
  have hm:=MovingNativeFields.relativeMeanInput_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm hΛ k mass ρ hmass hρ
    (fun z : (Fin k→ℝ)×W=>past z.2) (fun z=>age z.2) (hpast.comp measurable_snd) (hage.comp measurable_snd)
    (fun z=>θ z.2) (hθ.comp measurable_snd) Prod.fst measurable_fst (fun z=>ω z.2) (hω.comp measurable_snd)
  have hi:=hm.stronglyMeasurable.integral_prod_left'
    (μ:=Measure.pi (fun _ : Fin k=>volume.restrict (Ioc 0 (h:ℝ))))
  convert! hi.measurable using 1
  funext w
  exact absoluteAverage_eq_relative 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P A hA h Z htarget hstop F hF hFm k mass ρ hmass hρ past age θ ω w

end SHE.MovingMeanOldAverage

