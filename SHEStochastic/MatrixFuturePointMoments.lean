module

public import SHEStochastic.MatrixPointTargetContinuity
public import SHEStochastic.NativeScalarBDGAll
public import SHE.IntervalTimeMeasure
public import SHE.PastItoAlgebra
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MatrixFuturePointMoments
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hH : (H : ℝ) ≤ 1) (U : ℝ) (hU : 0 ≤ U)
    (Q : ℝ≥0 × Ω → Profile d) (hUpper : ∀ p, (Q p).upper ≤ U)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2))

def input (v s : ℝ≥0) (hs : s ≤ H) (x : HeatCircle) (i : d) : Process (E := Input (d := d)) F μ H :=
  PastItoInputs.post F μ H v (MatrixPointTargetContinuity.process F μ H hH U hU Q hUpper hQ s s hs x i)

def cap (U : ℝ) (v s : ℝ≥0) : ℝ := MatrixPointHeatInput.constant U*(2*((s : ℝ)-(v : ℝ))^(1/2 : ℝ))

include hU in
theorem cap_nonneg (v s : ℝ≥0) (hvs : v ≤ s) : 0 ≤ cap U v s :=
  mul_nonneg (MatrixPointHeatInput.constant_nonneg hU)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (sub_nonneg.mpr hvs) _))

theorem input_eq_sub (v s : ℝ≥0) (hs : s ≤ H) (hvs : v ≤ s) (x : HeatCircle) (i : d) :
    input F μ H hH U hU Q hUpper hQ v s hs x i=
      MatrixPointTargetContinuity.process F μ H hH U hU Q hUpper hQ s s hs x i-
        MatrixPointTargetContinuity.process F μ H hH U hU Q hUpper hQ v s hs x i :=
  PastItoAlgebra.post_stop_eq_sub F μ H v s hvs _

theorem input_ae (v s : ℝ≥0) (hs : s ≤ H) (x : HeatCircle) (i : d) :
    input F μ H hH U hU Q hUpper hQ v s hs x i =ᵐ[energyMeasure μ H]
      fun p => if v<p.1 ∧ p.1<s then MatrixPointHeatRows.row ((s : ℝ)-(p.1 : ℝ)) (Q p) x i else 0 := by
  filter_upwards [PastItoInputs.post_ae F μ H v
      (MatrixPointTargetContinuity.process F μ H hH U hU Q hUpper hQ s s hs x i),
    MatrixPointTargetContinuity.process_ae F μ H hH U hU Q hUpper hQ s s hs x i] with p hp hrow
  change input F μ H hH U hU Q hUpper hQ v s hs x i p=_ at hp
  rw [hp,hrow]
  by_cases h₁ : v<p.1 <;> by_cases h₂ : p.1<s <;> simp [h₁,h₂]

/-- The actual future vector point row retains the original short
interval variance gain, on the original full horizon and filtration. -/
theorem bracket_bound (v s : ℝ≥0) (hs : s ≤ H) (hvs : v ≤ s) (x : HeatCircle) (i : d) :
    ∀ᵐ ω ∂μ, (∫⁻ r, ENNReal.ofReal (‖input F μ H hH U hU Q hUpper hQ v s hs x i (r,ω)‖^2)
      ∂timeMeasure H) ≤ ENNReal.ofReal (cap U v s) := by
  have he := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (input_ae F μ H hH U hU Q hUpper hQ v s hs x i)
  filter_upwards [Measure.ae_ae_of_ae_prod he] with ω hω
  let K := MatrixPointHeatInput.constant U
  have hK : 0 ≤ K := MatrixPointHeatInput.constant_nonneg hU
  calc
    _ ≤ ∫⁻ r, ENNReal.ofReal K*(Ioc v s).indicator
        (fun r : ℝ≥0 => ENNReal.ofReal (((s : ℝ)-(r : ℝ))^(-(1/2 : ℝ)))) r ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [hω] with r hr
      dsimp only [Prod.swap] at hr
      change input F μ H hH U hU Q hUpper hQ v s hs x i (r,ω)=_ at hr
      rw [hr]
      by_cases ht : v<r ∧ r<s
      · rw [if_pos ht,Set.indicator_of_mem (show r ∈ Ioc v s from ⟨ht.1,ht.2.le⟩),← ENNReal.ofReal_mul hK]
        apply ENNReal.ofReal_le_ofReal
        exact MatrixPointHeatInput.row_bound (sub_pos.mpr (show (r : ℝ)<(s : ℝ) from ht.2))
          (by linarith [hH,(show (s : ℝ)≤(H : ℝ) from hs),r.2]) (Q (r,ω)) (hUpper (r,ω)) x i
      · rw [if_neg ht]
        simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0),ENNReal.ofReal_zero]
        exact bot_le
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator measurableSet_Ioc,
        timeMeasure_restrict_Ioc v hs,interval_causal_rpow_mass (by norm_num : (-1 : ℝ) < -(1/2 : ℝ)) hvs]
      norm_num only [show -(1/2 : ℝ)+1=1/2 by norm_num]
      rw [← ENNReal.ofReal_mul hK]
      congr 1
      unfold cap K
      ring

theorem coordinate_moment (N : FiniteScalarIto.Family F μ H (d × FiniteHaar.HaarNode))
    (v s : ℝ≥0) (hs : s ≤ H) (hvs : v ≤ s) (x : HeatCircle) (i : d) (p : ℕ) (hp : 0<p) :
    let J := FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis
    Integrable (fun ω => |J.integral (input F μ H hH U hU Q hUpper hQ v s hs x i) ω|^(2*p)) μ ∧
      (∫ ω, |J.integral (input F μ H hH U hU Q hUpper hQ v s hs x i) ω|^(2*p) ∂μ) ≤
        (NativeScalarBDGAll.constant p : ℝ)*(cap U v s)^p := by
  intro J
  have h := StandardTerminalBDGPower.moment_of_bracket_bound J
    (NativeScalarBDGAll.power N MatrixPredictableHaarRotation.basis p hp)
    (input F μ H hH U hU Q hUpper hQ v s hs x i) (cap_nonneg U hU v s hvs)
    (bracket_bound F μ H hH U hU Q hUpper hQ v s hs hvs x i)
  apply RealMomentBound.integral_bound μ _
    (by simpa only [Real.norm_eq_abs] using
      ((Lp.stronglyMeasurable (J.integral (input F μ H hH U hU Q hUpper hQ v s hs x i))).measurable.norm.pow_const (2*p)).aestronglyMeasurable)
    (fun ω => pow_nonneg (abs_nonneg _) _)
    (mul_nonneg (NativeScalarBDGAll.constant p).coe_nonneg (pow_nonneg (cap_nonneg U hU v s hvs) p))
  simpa only [Real.norm_eq_abs] using h

end SHEStochastic.MatrixFuturePointMoments
