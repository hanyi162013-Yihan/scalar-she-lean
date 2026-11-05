module

public import SHE.ScalarHeatSingleMultiplier

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.ScalarHeatSignedTrace
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
local instance scalarHeatSignedTrace_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatSignedTrace_unitPeriod : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance scalarHeatSignedTrace_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatSignedTrace_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

/-- The FIRST complete-Gamma term uses the SAME actual heat-band
family as the displaced-gradient second term. Its countable signed
Haar trace keeps the genuine massive negative INPUT energy, with the
original native time conversion visible. -/
theorem exists_gradient_signed_trace (m U : ℝ) (hm : 0<m) {ρ : ℝ} (hρ : 0<ρ) (hρhalf : ρ<1/2) :
    ∃ C : ℝ,0<C ∧ ∀ (a : ℝ→ℝ) (ha : BoundedSmooth a) (H β lo : ℝ)
      (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo),
    ∀ (hh : ∀ x y,|a x-a y|≤H*|x-y|^β),∀ (j : ℕ)
      (σ x : P×HeatCircle→ℝ) (hσm : Measurable σ) (hxm : Measurable x) (p : P),
    ∀ (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z)),∀ (Λ t : ℝ) (hΛ : 1≤Λ) (ht : 0<t),t≤1→
      ∀ c d : FiniteHaar.EllipticField m U,
    let b:=ScalarHeatSingleMultiplier.multiplier a j σ x p
    let B:=(H*ScalarHeatBandEnvelope.constant β 0)*CompactMollifier.radius (j+1)^(β-1)*
      decay (CompactMollifier.radius (j+1)) lo ((3-β)/2)
    let hb:=ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσm hxm p hσ
    let col:=fun q : FiniteHaar.HaarNode=>OneInputOperator.besselHalf Λ ρ hΛ hρ.le
      (NativeMultiplierTrace.multiplier b B hb (circleHeatOperator t ht.le
        (CircleNormalization.push (FiniteHaar.globalHaarColumn q d.1-FiniteHaar.globalHaarColumn q c.1))))
    Summable (fun q=>‖col q‖^2) ∧
      (∑' q,‖col q‖^2)≤C*B^2*(NativeHeatSpan.clock t)^(-(1/2:ℝ))*NativeSignedHaarProcess.inputEnergy hΛ hρ.le c d := by
  obtain ⟨C,hC,htrace⟩:=NativeMultiplierTrace.exists_signed_multiplier_trace m U hm hρ hρhalf
  refine ⟨C,hC,?_⟩
  intro a ha H β lo hH hβ hβ1 hlo hh j σ x hσm hxm p hσ Λ t hΛ ht ht1 c d b B hb col
  have hB : 0≤B:=mul_nonneg
    (mul_nonneg (mul_nonneg hH (ScalarHeatBandEnvelope.constant_nonneg β 0))
      (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _))
    (le_min zero_le_one (rpow_nonneg (div_nonneg hlo.le (sq_nonneg _)) _))
  exact htrace Λ t hΛ ht ht1 b B hB hb c d

end SHE.ScalarHeatSignedTrace
