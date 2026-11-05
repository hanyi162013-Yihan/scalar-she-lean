module

public import SHE.MovingMeanThetaEnergy

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingMeanPhysicalField
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingMeanPhysicalField_realSigma : MeasurableSpace RealL2 := borel _
local instance movingMeanPhysicalField_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingMeanPhysicalField_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingMeanPhysicalField_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingMeanPhysicalField_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingMeanPhysicalField_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)

local instance movingMeanPhysicalField_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingMeanPhysicalField_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingMeanPhysicalField_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingMeanPhysicalField_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]



open Set CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
  PhysicalScoreChain ControlledOldIntervals
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




local notation "Avg"=>MovingMeanThetaEnergy.thetaValue 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP h Z htarget hstop F hF hFm

/-- Actual physical moving-past window; current and past are both
kept within the original stochastic clock. -/
def valid (H h : ℝ≥0) (v s : ℝ) : Prop:=0≤v ∧ 0<s ∧ s<(h:ℝ) ∧ v+(h:ℝ)≤(H:ℝ)
instance valid_decidable (H h : ℝ≥0) (v s : ℝ) : Decidable (valid H h v s) := inferInstanceAs (Decidable (_∧_∧_∧_))

def field (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (z : ℝ×(ℝ×Ω)) : CircleL2 :=
  if valid H h z.1 z.2.1 then Avg k mass ρ hmass hρ (z.1.toNNReal,(z.2.1.toNNReal,z.2.2)) else 0
local notation "Fv"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP h Z htarget hstop F hF hFm

theorem field_measurable (hΛ : 0≤Λ) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (Fv k mass ρ hmass hρ) := by
  have hmap : Measurable (fun z : ℝ×(ℝ×Ω)=>(z.1.toNNReal,(z.2.1.toNNReal,z.2.2))) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      ((measurable_real_toNNReal.comp measurable_snd.fst).prodMk measurable_snd.snd)
  have hm:=(MovingMeanThetaEnergy.thetaValue_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP h Z htarget hstop F hF hFm hΛ k mass ρ hmass hρ).comp hmap
  have hv : MeasurableSet {z : ℝ×(ℝ×Ω)|valid H h z.1 z.2.1} :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const measurable_snd.fst).inter
        ((measurableSet_lt measurable_snd.fst measurable_const).inter
          (measurableSet_le (measurable_fst.add_const (h:ℝ)) measurable_const)))
  exact hm.ite hv measurable_const

theorem field_of_valid (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v s : ℝ) (hv : valid H h v s) (ω : Ω) :
    Fv k mass ρ hmass hρ (v,(s,ω))=
      Avg k mass ρ hmass hρ (v.toNNReal,(s.toNNReal,ω)) := if_pos hv

theorem field_zero (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (v s : ℝ) (hv : ¬valid H h v s) (ω : Ω) :
    Fv k mass ρ hmass hρ (v,(s,ω))=0 := if_neg hv

end SHE.MovingMeanPhysicalField

