module

public import SHEStochastic.ScalarStoppedMomentKernels
public import SHEStochastic.ScalarMomentBielecki

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarStoppedMildVolterra
open MeasureTheory Set SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open ScalarStoppedMildMoment ScalarStoppedMomentProfiles ScalarStoppedMomentKernels
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "Noise" => Lp ℝ 2 (haarAddCircle (T := 2*Real.pi))
local notation "tm" => PredictableL2.timeMeasure

def driftWeight (H L : ℝ≥0) : ℝ := (H : ℝ)*(2*(L : ℝ)^2)*(H : ℝ)^(1/2 : ℝ)
def heatWeight (H : ℝ≥0) (K : ℝ) : ℝ :=
  ((H : ℝ)^(1/2 : ℝ)+2*HeatTrace.fractionalGaussianIntegral 0)*K

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  (hc : ∀ ω,Continuous (fun t => W t ω))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
  (b : ScalarLinearGrowthDriftField.Data H) (a : ℝ≥0 → Ω → ℝ)
  (u₀ : RealL2)

local notation "v" => ScalarStoppedHeatFourierInput.input F μ H W hW hc hg hβ hβ₁
local notation "K" => (4*(‖g 0‖+(C : ℝ))^2)

omit [IsProbabilityMeasure μ] in
private theorem drift_bound (L : ℝ≥0) (N : ℕ) (t : ℝ≥0) (ht : t≤H) :
    ENNReal.ofReal ((t : ℝ)*(2*(L : ℝ)^2))*(∫⁻ s,growth μ W N s ∂tm t) ≤
      ENNReal.ofReal (driftWeight H L)*(∫⁻ s,ageKernel t s*growth μ W N s ∂tm t) := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [timeMeasure_ae_mem t,(tm t).ae_ne t] with s hs hst
  have hts : 0<(t : ℝ)-(s : ℝ) := sub_pos.mpr (by exact_mod_cast lt_of_le_of_ne hs.2 hst)
  have htR : (t : ℝ)≤H := by exact_mod_cast ht
  have hrH : (t : ℝ)-(s : ℝ)≤H := (sub_le_self _ s.property).trans htR
  have hpow : 1≤(H : ℝ)^(1/2 : ℝ)*((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ)) := by
    rw [Real.rpow_neg hts.le,←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos hts _),one_mul]
    exact Real.rpow_le_rpow hts.le hrH (by norm_num)
  rw [←mul_assoc (ENNReal.ofReal (driftWeight H L)),ageKernel,←ENNReal.ofReal_mul (by unfold driftWeight; positivity)]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (H : ℝ)*(2*(L : ℝ)^2) := by gcongr
    _ ≤ ((H : ℝ)*(2*(L : ℝ)^2))*((H : ℝ)^(1/2 : ℝ)*((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ))) :=
      le_mul_of_one_le_right (by positivity) hpow
    _ = _ := by unfold driftWeight; ring

/-- The original stopped mild rows yield the causal second-moment inequality.
All constants are independent of the norm exit and of the drift multiplier. -/
theorem profile
    (heq : Equation F μ H W hW hc hg hβ hβ₁ J b a u₀)
    (ham : ∀ ω,Measurable (fun s => a s ω)) (ha : ∀ s ω,|a s ω|≤1)
    (N : ℕ) (t : ℝ≥0) (ht : t≤H) :
    1+second μ W N t ≤ ENNReal.ofReal (1+3*‖u₀‖^2) +
      ENNReal.ofReal (3*(driftWeight H b.growth+heatWeight H K))*
        (∫⁻ s,ageKernel t s*(1+second μ W N s) ∂tm t) := by
  let A := ENNReal.ofReal (‖u₀‖^2)
  let d (ω : Ω) := ENNReal.ofReal ((t : ℝ)*
    ∫ s,2*(b.growth : ℝ)^2*liveGrowth W N s ω ∂tm t)
  let y (n : ℤ) (ω : Ω) := ENNReal.ofReal (((J.integral (v N t Complex.reCLM n)) ω)^2+
    ((J.integral (v N t Complex.imCLM n)) ω)^2)
  let Y (ω : Ω) := ∑' n : ℤ,y n ω
  have hy (n : ℤ) : Measurable (y n) :=
    (((Lp.stronglyMeasurable (J.integral (v N t Complex.reCLM n))).measurable.pow_const 2).add
      ((Lp.stronglyMeasurable (J.integral (v N t Complex.imCLM n))).measurable.pow_const 2)).ennreal_ofReal
  have hY : Measurable Y := Measurable.tsum hy
  let I := ∫⁻ s,ageKernel t s*growth μ W N s ∂tm t
  have hI : I≤∫⁻ s,ageKernel t s*(1+second μ W N s) ∂tm t := by
    apply lintegral_mono
    intro s
    exact mul_le_mul_right (growth_le μ W N s) _
  have hd : (∫⁻ ω,d ω ∂μ)≤ENNReal.ofReal (driftWeight H b.growth)*I := by
    unfold d
    rw [ScalarStoppedMomentKernels.drift F μ W hW hc N b.growth t]
    exact drift_bound μ H W b.growth N t ht
  have hS : (∫⁻ ω,Y ω ∂μ)≤ENNReal.ofReal (heatWeight H K)*I :=
    (ScalarStoppedHeatItoEnergy.bound F μ H W hW hc hg hβ hβ₁ N t J).trans
      (ScalarStoppedMomentKernels.heat F μ W hW hc N H t ht K (by positivity))
  have hstep : second μ W N t ≤ 3*(A+
      ENNReal.ofReal (driftWeight H b.growth)*I+ENNReal.ofReal (heatWeight H K)*I) := by
    calc
      _ ≤ ∫⁻ ω,3*(A+d ω+Y ω) ∂μ :=
        lintegral_mono_ae (path_bound F μ H W hW hc hg hβ hβ₁ J b a u₀ heq ham ha N t ht)
      _ = 3*(A+(∫⁻ ω,d ω ∂μ)+(∫⁻ ω,Y ω ∂μ)) := by
        rw [lintegral_const_mul' _ _ (by simp),lintegral_add_right _ hY,
          lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
      _ ≤ _ := by gcongr
  have hD : 0≤driftWeight H b.growth := by unfold driftWeight; positivity
  have hGaussian := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0 : ℝ)<1/2)).le
  have hQ : 0≤heatWeight H K := by unfold heatWeight; positivity
  calc
    _ ≤ 1+3*(A+ENNReal.ofReal (driftWeight H b.growth)*I+ENNReal.ofReal (heatWeight H K)*I) :=
      add_le_add_right hstep _
    _ = ENNReal.ofReal (1+3*‖u₀‖^2)+ENNReal.ofReal (3*(driftWeight H b.growth+heatWeight H K))*I := by
      rw [ENNReal.ofReal_add zero_le_one (by positivity),ENNReal.ofReal_one,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤3),ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤3),
        ENNReal.ofReal_add hD hQ]
      rw [show ENNReal.ofReal (3 : ℝ) = 3 by norm_num]
      unfold A
      ring
    _ ≤ _ := by gcongr

end SHEStochastic.ScalarStoppedMildVolterra
