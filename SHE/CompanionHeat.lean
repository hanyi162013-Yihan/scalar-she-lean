module

public import SHE.HaarL2Heat
public import SHE.CoefficientFields
public import SHE.ConvolutionEnergy
public import SHE.RootConvolution

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.CompanionHeat
open MeasureTheory Set AddCircle CircleHeat FiniteHaar CoefficientFields LowBands
open scoped ENNReal NNReal
local instance companionHeat_circlePositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def nonlinearColumn (a : ℝ → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ z,|a z| ≤ M)
    (u v : StateL2) (j : HaarNode) : CircleL2 :=
  globalSignedColumn j (coefficient a ha M hM u) (coefficient a ha M hM v)

theorem smooth_heat_columns {a : ℝ → ℝ} (ha : Measurable a) {ell M : ℝ} (hell : 0 < ell)
    (haB : ∀ z,ell ≤ a z ∧ a z ≤ M) {L : ℝ≥0}
    (hLip : LipschitzWith L (fun z => (a z:ℂ))) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (u v : StateL2) :
    let hM : ∀ z,|a z| ≤ M := fun z => by rw [abs_of_nonneg (hell.le.trans (haB z).1)]; exact (haB z).2
    Summable (fun j : HaarNode => ‖heat t (nonlinearColumn a ha M hM u v j)‖^2) ∧
      (∑' j : HaarNode,‖heat t (nonlinearColumn a ha M hM u v j)‖^2) ≤
        (signedL2HeatConstant ell M*(L:ℝ)^2)*t^(-(1/2:ℝ))*‖u-v‖^2 := by
  intro hM
  have hh := global_signed_heat_L2 ht ht1 (coefficient a ha M hM u) (coefficient a ha M hM v)
    ell M hell (coefficient_real a ha M hM u) (coefficient_real a ha M hM v)
    (coefficient_elliptic a ha M hM u ell M haB) (coefficient_elliptic a ha M hM v ell M haB)
  have hM0 : 0 ≤ M := hell.le.trans ((haB 0).1.trans (haB 0).2)
  have hC : 0 ≤ signedL2HeatConstant ell M := by unfold signedL2HeatConstant; positivity
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (coefficient_lipschitz_bound a ha M hM hLip u v) 2
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ signedL2HeatConstant ell M*t^(-(1/2:ℝ))*((L:ℝ)*‖u-v‖)^2 :=
      mul_le_mul_of_nonneg_left hnorm (mul_nonneg hC (Real.rpow_nonneg ht.le _))
    _ = _ := by ring

/-- The genuine integrable causal singularity in the smooth companion's
stochastic Picard map. -/
def picardKernel (h u : ℝ) : ℝ≥0∞ :=
  (Ioc (0:ℝ) h).indicator (fun u => ENNReal.ofReal (u^(-(1/2:ℝ)))) u

theorem picardKernel_measurable (h : ℝ) : Measurable (picardKernel h) :=
  (ENNReal.continuous_ofReal.measurable.comp (real_rpow_measurable _)).indicator measurableSet_Ioc

theorem picardKernel_mass {h : ℝ} (hh : 0 ≤ h) :
    (∫⁻ u : ℝ,picardKernel h u)=ENNReal.ofReal (2*h^(1/2:ℝ)) := by
  have hi : IntervalIntegrable (fun u : ℝ => u^(-(1/2:ℝ))) volume 0 h :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hh).mp hi
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) h)] (fun u : ℝ => u^(-(1/2:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact Real.rpow_nonneg hu.1.le _
  simp only [picardKernel]
  rw [lintegral_indicator measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi' hnn,← intervalIntegral.integral_of_le hh,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2:ℝ)))]
  congr 1
  norm_num
  ring

theorem picard_causal_energy {h : ℝ} (hh : 0 ≤ h) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t in Ioc (0:ℝ) h,∫⁻ s in Ioc (0:ℝ) t,picardKernel h (t-s)*F s) ≤
      ENNReal.ofReal (2*h^(1/2:ℝ))*(∫⁻ s in Ioc (0:ℝ) h,F s) := by
  simpa only [picardKernel_mass hh] using
    causal_convolution_energy_bound (picardKernel h) F (picardKernel_measurable h) hF h

end SHE.CompanionHeat
