module

public import SHE.NativeStoppedBracket
public import SHE.PredictableBracketValue
public import SHE.PastItoInputs
public import SHE.IntervalTimeMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativePastBracket
open Set MeasureTheory PredictableL2 StoppedFourier FiniteHaar ProfileVariance
open PastItoInputs
open scoped NNReal ENNReal
local instance nativePastBracket_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- The actual native observation noise after any deterministic past
time v has bracket of order sqrt(q-v). All inputs remain in the SAME
full horizon H, and the original heat target need only exceed q. -/
theorem bracket_bound_of_ae {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1)
    {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
    (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
    {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle)
    (u : Process (E := RealHaarInput) 𝓕 μ H)
    (hu : ∀ᵐ p : ℝ≥0×Ω ∂energyMeasure μ H,u p=if v<p.1 then NativeObservationProcess.integrand hell f T (q:ℝ) x p else 0) :
    ∀ᵐ (ω : Ω) ∂μ,PredictableL2.bracket u ω≤
      ENNReal.ofReal (upperConstant*M*((q:ℝ)-(v:ℝ))^(1/2:ℝ)) := by
  have he := hu
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  unfold PredictableL2.bracket
  let K : ℝ := M*(1+heatConstant)
  have hK : 0≤K := mul_nonneg hM (by linarith [heatConstant_pos])
  calc
    _ ≤ ∫⁻ s : ℝ≥0,ENNReal.ofReal K*(Ioc v q).indicator
        (fun r : ℝ≥0 => ENNReal.ofReal (((q:ℝ)-(r:ℝ))^(-(1/2:ℝ)))) s ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [hω] with s hrow
      dsimp only [Prod.swap] at hrow
      rw [hrow]
      by_cases hvs : v<s
      · rw [if_pos hvs,NativeObservationProcess.integrand_eq hell f hT]
        by_cases hsq : s<q
        · have hsq' : (s:ℝ)<(q:ℝ) := by exact_mod_cast hsq
          rw [ite_eq_left hsq',indicator_of_mem (show s∈Ioc v q from ⟨hvs,hsq.le⟩),← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          have hb := NativeObservationProcess.row_norm_sq_bound hell (f (s,ω))
            (T := T) (r := (s:ℝ)) (t := (s:ℝ)+T-(q:ℝ)) (by linarith) (by linarith) x
          rw [show T-((s:ℝ)+T-(q:ℝ))=(q:ℝ)-(s:ℝ) by ring] at hb
          have hage : (q:ℝ)-(s:ℝ)≤1 := by
            have hvs' : (v:ℝ)<(s:ℝ) := by exact_mod_cast hvs
            linarith
          have hpow := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (sub_pos.mpr hsq') hage
            (by norm_num : -(1/2:ℝ)≤0)
          have hm := mul_le_mul_of_nonneg_left hpow hM
          dsimp [K]
          nlinarith
        · have hsq' : ¬(s:ℝ)<(q:ℝ) := by exact_mod_cast hsq
          rw [ite_eq_right hsq']
          simp
      · rw [if_neg hvs]
        simp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Ioc,
        timeMeasure_restrict_Ioc v hqH,interval_causal_rpow_mass (by norm_num : (-1:ℝ) < -(1/2:ℝ)) hvq]
      norm_num only [show -(1/2:ℝ)+1=1/2 by norm_num]
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      unfold K ProfileVariance.upperConstant
      ring

end SHE.NativePastBracket
