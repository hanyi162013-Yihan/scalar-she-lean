module

public import SHEStochastic.ScalarDriftNativeDirection
public import SHEStochastic.ScalarStoppedMomentUniform
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarSignedControl
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {H : ℝ≥0}

def scale (b : ScalarLinearGrowthDriftField.Data H) (σ : ℝ) (hσ : |σ|≤1) :
    ScalarLinearGrowthDriftField.Data H where
  value p := σ*b.value p
  measurable := b.measurable.const_mul _
  growth := b.growth
  bound t ht x z := by
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hσ).trans (b.bound t ht x z)

theorem field_scale (b : ScalarLinearGrowthDriftField.Data H) (σ : ℝ) (hσ : |σ|≤1) (p : ℝ≥0×RealL2) :
    ScalarLinearGrowthDriftField.field (scale b σ hσ) p =
      σ • ScalarLinearGrowthDriftField.field b p := by
  apply Lp.ext
  filter_upwards [ScalarLinearGrowthDriftField.field_ae (scale b σ hσ) p,
    ScalarLinearGrowthDriftField.field_ae b p,Lp.coeFn_smul σ (ScalarLinearGrowthDriftField.field b p)]
    with x h₁ h₂ hs
  rw [h₁,hs,Pi.smul_apply,h₂]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (b : ScalarLinearGrowthDriftField.Data H)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "tm" => PredictableL2.timeMeasure
local notation "row" => ScalarDriftNativeDirection.row b (Function.uncurry W)

include hW in
/-- A signed Borel control with its actual time-fibre energy. Any
equivalent probability with the uniform stopped moment bound inherits
a deterministic control-energy bound. -/
theorem exists_signed (σ : ℝ) (hσ : |σ|≤1)
    (hM : (∫⁻ p,ENNReal.ofReal (‖W p.1 p.2‖^2) ∂energyMeasure μ H)<⊤) :
    ∃ u : Lp Noise 2 νin,u =ᵐ[νin] (fun p => σ • row p) ∧
      ∀ (Q : Measure Ω) [IsProbabilityMeasure Q],Q ≪ μ → ∀ R : ℝ,0≤R →
        (∫⁻ p,ENNReal.ofReal (‖W p.1 p.2‖^2) ∂energyMeasure Q H)≤ENNReal.ofReal R →
        (∫⁻ ω,ENNReal.ofReal (NativeEnergy.energy u ω) ∂Q)≤
          ENNReal.ofReal (2*(b.growth : ℝ)^2*((H : ℝ)+R)) := by
  have hI := ScalarStoppedMomentUniform.integrable_sq F μ H W hW hM
  obtain ⟨u,hu,hE⟩ := ScalarDriftNativeDirection.exists_control F μ (scale b σ hσ)
    (Function.uncurry W) hW hI
  refine ⟨u,hu.mono ?_,?_⟩
  · intro p hp
    rw [hp,ScalarDriftNativeDirection.row,field_scale,map_smul]
    rfl
  · intro Q _ hQ R hR hE₂
    let f (p : ℝ≥0×Ω) := ENNReal.ofReal (‖W p.1 p.2‖^2)
    have hf : Measurable f := ((hW.mono (predictable_le_product F)).norm.pow 2).measurable.ennreal_ofReal
    have hs : MathFin.ItoIntegralCLM.timeMeasure_T H = tm H := (SHEStochastic.timeMeasure_eq H).symm
    have he (t : ℝ≥0) (ω : Ω) : ENNReal.ofReal (2*(b.growth : ℝ)^2*(1+‖W t ω‖^2)) =
        ENNReal.ofReal (2*(b.growth : ℝ)^2)*(1+f (t,ω)) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add zero_le_one (sq_nonneg _),ENNReal.ofReal_one]
    apply (hE Q hQ).trans
    change (∫⁻ ω,∫⁻ t,ENNReal.ofReal (2*(b.growth : ℝ)^2*(1+‖W t ω‖^2))
        ∂MathFin.ItoIntegralCLM.timeMeasure_T H ∂Q)≤_
    rw [hs]
    simp_rw [he,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm : Measurable (fun p : ℝ≥0×Ω => 1+f p) := measurable_const.add hf
    rw [←lintegral_prod_symm _ hm.aemeasurable,lintegral_add_left measurable_const,lintegral_const,
      Measure.prod_apply MeasurableSet.univ]
    simp only [Set.preimage_univ,
      measure_univ,lintegral_const,one_mul]
    have hAdd : ENNReal.ofReal ((H : ℝ)+R)=ENNReal.ofReal (H : ℝ)+ENNReal.ofReal R :=
      ENNReal.ofReal_add H.property hR
    rw [timeMeasure_mass,ENNReal.ofReal_mul (q := (H : ℝ)+R)
      (show 0≤2*(b.growth : ℝ)^2 by positivity),hAdd]
    exact mul_le_mul_right (add_le_add_right hE₂ _) _

end SHEStochastic.ScalarSignedControl
