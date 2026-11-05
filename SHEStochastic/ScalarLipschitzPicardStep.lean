module

public import SHEStochastic.ScalarLipschitzMomentBall

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzPicardStep
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzItoMoment ScalarLipschitzRawBounds
  ScalarLipschitzDampedEnergy ScalarLipschitzDampedMoments ScalarLipschitzMomentBall
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "tm" => PredictableL2.timeMeasure
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)

omit [MeasurableSpace Ω] [Countable I] [DecidableEq I] [IsProbabilityMeasure μ] in
theorem weight_choice :
    ∃ γ : ℝ,0<γ ∧ heatConstant (H : ℝ)*(C : ℝ)^2*BieleckiKernel.mass γ≤1/4 ∧
      (2 : ℝ)^16*growthConstant g (C : ℝ) (H : ℝ) γ≤1/4 := by
  have h₁ := BieleckiKernel.mass_tends_zero.const_mul (heatConstant (H : ℝ)*(C : ℝ)^2)
  have h₂ := (growthConstant_tendsto g (C : ℝ) (H : ℝ)).const_mul ((2 : ℝ)^16)
  rw [mul_zero] at h₁ h₂
  obtain ⟨γ,hγ,h₁',h₂'⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((h₁.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))).and
      (h₂.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/4))))).exists
  exact ⟨γ,hγ,h₁'.le,h₂'.le⟩

def forcing (u₀ : RealL2) (t : ℝ≥0) : RealL2 := NativeHeatObservation.heat (t : ℝ) u₀

theorem forcing_continuous (u₀ : RealL2) : Continuous (forcing u₀) := by
  have ht : Continuous (fun t : ℝ≥0 => (t : ℝ)/NativeHeatObservation.timeScale) :=
    NNReal.continuous_coe.div_const NativeHeatObservation.timeScale
  have he : Continuous (fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,u₀)) :=
    ht.prodMk continuous_const
  have hf : Continuous ((fun p : ℝ×RealL2 => RealHeat.realHeat p.1 p.2) ∘
      (fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,u₀))) :=
    RealHeat.continuous_realHeat_action.comp he
  exact hf

theorem forcing_bound (u₀ : RealL2) (t : ℝ≥0) : ‖forcing u₀ t‖≤‖u₀‖ :=
  RealHeat.realHeat_contraction _ _

theorem forcing_weighted {γ : ℝ} (hγ : 0≤γ) (u₀ : RealL2) (t : ℝ≥0) :
    weightedMoment (μ := μ) γ (fun s (_ : Ω) => forcing u₀ s) t≤ENNReal.ofReal (‖u₀‖^16) := by
  unfold weightedMoment moment
  rw [lintegral_const,measure_univ,mul_one]
  calc
    _ ≤ 1*ENNReal.ofReal (‖u₀‖^16) := by
      gcongr
      · exact pow_le_one₀ bot_le (timeWeight_le_one hγ t)
      · exact forcing_bound u₀ t
    _ = _ := one_mul _

theorem coefficient_moment {γ : ℝ} (hγ : 0<γ) {D : ℝ} (hD : 0≤D)
    (U : ℝ≥0 → Ω → RealL2) (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hM : ∀ᵐ t ∂tm H,weightedMoment (μ := μ) γ U t≤ENNReal.ofReal D) :
    ∃ M : ℝ,0≤M ∧ ∀ᵐ t ∂tm H,(∫⁻ ω,(coeffSquare hg U (t,ω))^8 ∂μ)≤ENNReal.ofReal M := by
  let E := Real.exp (16*γ*(H : ℝ))
  let A := (growth g C)^8*2^8
  have hA : 0≤A := by dsimp only [A]; positivity
  refine ⟨A*(1+E*D),by dsimp only [E]; positivity,?_⟩
  filter_upwards [hM,timeMeasure_ae_mem H] with t ht htime
  have hUt : Measurable (U t) :=
    (hU.mono (predictable_le_product F)).measurable.comp (measurable_const.prodMk measurable_id)
  have hN : moment 16 (U t) μ≤ENNReal.ofReal (E*D) := by
    rw [weightedMoment_unweight γ U t,timeWeight_pow]
    have hExp : Real.exp (-16*(-γ)*(t : ℝ))≤E := by
      apply Real.exp_le_exp.mpr
      have htH : (t : ℝ)≤(H : ℝ) := by exact_mod_cast htime.2
      nlinarith [mul_nonneg hγ.le (sub_nonneg.mpr htH)]
    rw [ENNReal.ofReal_mul (q := D) (show 0≤E from (Real.exp_pos _).le)]
    exact mul_le_mul (ENNReal.ofReal_le_ofReal hExp) ht bot_le bot_le
  refine (coeffSquare_eighth (μ := μ) hg U t hUt).trans ?_
  have hE : 0≤E*D := mul_nonneg (Real.exp_nonneg _) hD
  rw [ENNReal.ofReal_mul (q := 1+E*D) hA,ENNReal.ofReal_add zero_le_one hE,ENNReal.ofReal_one]
  exact mul_le_mul_right (add_le_add le_rfl hN) _

/-- One original nonlinear Picard step maps the moment ball into
itself, and has simultaneously continuous adapted paths. -/
theorem exists_step (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    {γ D : ℝ} (hγ : 0<γ) (hD : 1≤D)
    (hsmall : (2 : ℝ)^16*growthConstant g (C : ℝ) (H : ℝ) γ≤1/4)
    (u₀ : RealL2) (h₀ : 2*(2 : ℝ)^16*‖u₀‖^16≤D)
    (U : ℝ≥0 → Ω → RealL2) (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
    (hM : ∀ᵐ t ∂tm H,weightedMoment (μ := μ) γ U t≤ENNReal.ofReal D) :
    ∃ X : ℝ≥0 → Ω → RealL2, (∀ ω,Continuous (fun t => X t ω)) ∧ StronglyAdapted F X ∧
      (∀ t, t≤H → weightedMoment (μ := μ) γ X t≤ENNReal.ofReal D) ∧
      ∀ t, t≤H → ∃ hE : Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H),
        X t=ᵐ[μ] fun ω => forcing u₀ t+(ito e P).integral (input e hg U hU t hE) ω := by
  have hD0 : 0≤D := zero_le_one.trans hD
  obtain ⟨M,hM₀,hCM⟩ := coefficient_moment (H := H) hg hγ hD0 U hU hM
  obtain ⟨Z,hc,ha,hZ⟩ := ScalarLipschitzTimeMoments.exists_version e P hg U hU M hM₀ hCM hH hn
  let X : ℝ≥0 → Ω → RealL2 := fun t ω => forcing u₀ t+Z t ω
  refine ⟨X,fun ω => (forcing_continuous u₀).add (hc ω),fun t => stronglyMeasurable_const.add (ha t),?_,?_⟩
  · intro t ht
    have hm := convolution_bound e P hg U hU hγ D hD0 hM t ht
      (raw_integrable e hg U hU ENNReal.ofReal_ne_top hCM t ht)
    have hZ' : weightedMoment (μ := μ) γ Z t≤ENNReal.ofReal (growthConstant g (C : ℝ) (H : ℝ) γ*(1+D)) := by
      unfold weightedMoment
      rw [moment_congr (hZ t ht)]
      exact hm
    have hX := weightedMoment_add (μ := μ) γ (fun s (_ : Ω) => forcing u₀ s) Z t measurable_const
      (((ha t).mono (F.le t)).measurable)
    refine hX.trans ((mul_le_mul_right (add_le_add (forcing_weighted hγ.le u₀ t) hZ') _).trans ?_)
    have hA : 0≤growthConstant g (C : ℝ) (H : ℝ) γ := growthConstant_nonneg _ _ _ _
    rw [←ENNReal.ofReal_add (pow_nonneg (norm_nonneg _) _) (by positivity),
      ←ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_right hsmall (show 0≤1+D by linarith)
    nlinarith only [h,h₀,hD]
  · intro t ht
    exact ⟨raw_integrable e hg U hU ENNReal.ofReal_ne_top hCM t ht,
      (hZ t ht).fun_comp (fun z => forcing u₀ t+z)⟩

end SHEStochastic.ScalarLipschitzPicardStep
