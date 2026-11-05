module

public import SHEStochastic.ScalarLipschitzRawBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzDampedEnergy
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzHeatColumns ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzItoMoment
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

def timeWeight (γ : ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-2*γ*(t : ℝ)))

theorem timeWeight_measurable (γ : ℝ) : Measurable (timeWeight γ) := by
  unfold timeWeight
  fun_prop

theorem timeWeight_ne_zero (γ : ℝ) (t : ℝ≥0) : timeWeight γ t≠0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem timeWeight_le_one {γ : ℝ} (hγ : 0≤γ) (t : ℝ≥0) : timeWeight γ t≤1 := by
  rw [←ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by nlinarith [t.property]))

theorem timeWeight_factor (γ : ℝ) (s t : ℝ≥0) :
    timeWeight γ t=ENNReal.ofReal (Real.exp (-2*γ*((t : ℝ)-(s : ℝ))))*timeWeight γ s := by
  unfold timeWeight
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
  congr 2
  ring

theorem timeWeight_inverse (γ : ℝ) (t : ℝ≥0) : timeWeight γ t*timeWeight (-γ) t=1 := by
  unfold timeWeight
  rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add,
    show -2*γ*(t : ℝ)+(-2)*(-γ)*(t : ℝ)=0 by ring,Real.exp_zero,ENNReal.ofReal_one]

theorem timeWeight_pow (γ : ℝ) (t : ℝ≥0) :
    (timeWeight γ t)^8=ENNReal.ofReal (Real.exp (-16*γ*(t : ℝ))) := by
  unfold timeWeight
  rw [←ENNReal.ofReal_pow (Real.exp_nonneg _),←Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem damped_nonzero {H : ℝ≥0} (γ : ℝ) {s t : ℝ≥0} (hst : s<t) (ht : t≤H) :
    BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ)) =
      ENNReal.ofReal (Real.exp (-2*γ*((t : ℝ)-(s : ℝ)))*((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ))) := by
  have ha : 0<(t : ℝ)-(s : ℝ) := sub_pos.mpr (by exact_mod_cast hst)
  have hb : (t : ℝ)-(s : ℝ)≤H := (sub_le_self _ s.property).trans (by exact_mod_cast ht)
  exact indicator_of_mem (show (t : ℝ)-(s : ℝ)∈Ioc (0 : ℝ) H from ⟨ha,hb⟩) _

theorem damped_zero {H : ℝ≥0} (γ : ℝ) {s t : ℝ≥0} (hst : t ≤ s) :
    BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))=0 := by
  have ha : (t : ℝ)-(s : ℝ)≤0 := sub_nonpos.mpr (by exact_mod_cast hst)
  exact indicator_of_notMem (fun (hm : (t : ℝ)-(s : ℝ)∈Ioc (0 : ℝ) H) => (not_lt_of_ge ha) hm.1) _

variable {Ω I : Type*} [MeasurableSpace Ω]
  {H : ℝ≥0} (e : HilbertBasis I ℝ Noise)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)

omit [MeasurableSpace Ω] in
theorem raw_difference {t : ℝ≥0} (ht : t≤H) (γ : ℝ)
    (U V : ℝ≥0 → Ω → RealL2) (p : ℝ≥0×Ω) :
    timeWeight γ t*ENNReal.ofReal (‖raw e hg U t p-raw e hg V t p‖^2)≤
      ENNReal.ofReal (heatConstant (H : ℝ)*(C : ℝ)^2)*
        BieleckiKernel.kernel H γ ((t : ℝ)-(p.1 : ℝ))*
        (timeWeight γ p.1*ENNReal.ofReal (‖U p.1 p.2-V p.1 p.2‖^2)) := by
  by_cases hs : p.1<t
  · let r := (t : ℝ)-(p.1 : ℝ)
    have hr : 0<r := sub_pos.mpr (by exact_mod_cast hs)
    have hrH : r≤H := (sub_le_self _ p.1.property).trans (by exact_mod_cast ht)
    have hk : 0≤heatConstant (H : ℝ)*r^(-(1/2 : ℝ)) :=
      mul_nonneg (heatConstant_nonneg H.property) (Real.rpow_nonneg hr.le _)
    have hC := pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_difference hg (U p.1 p.2) (V p.1 p.2)) 2
    rw [mul_pow] at hC
    have he : ‖raw e hg U t p-raw e hg V t p‖^2≤
        (heatConstant (H : ℝ)*r^(-(1/2 : ℝ)))*((C : ℝ)^2*‖U p.1 p.2-V p.1 p.2‖^2) := by
      rw [raw,raw,←kernel_sub]
      exact (kernel_bound e hr hrH _).trans (mul_le_mul_of_nonneg_left hC hk)
    apply (mul_le_mul_right (ENNReal.ofReal_le_ofReal he) _).trans_eq
    rw [timeWeight_factor γ p.1 t,damped_nonzero γ hs ht]
    have hk0 : 0≤heatConstant (H : ℝ) := heatConstant_nonneg H.property
    have hk1 := ENNReal.ofReal_mul (q := r^(-(1/2 : ℝ))) hk0
    have hk2 := ENNReal.ofReal_mul (q := (C : ℝ)^2) hk0
    rw [ENNReal.ofReal_mul hk,hk1,hk2,ENNReal.ofReal_mul (sq_nonneg (C : ℝ)),
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    dsimp only [r]
    ring
  · rw [raw_zero e hg U t (le_of_not_gt hs),raw_zero e hg V t (le_of_not_gt hs),sub_zero,norm_zero]
    simp

omit [MeasurableSpace Ω] in
theorem raw_growth {t : ℝ≥0} (ht : t≤H) (γ : ℝ) (U : ℝ≥0 → Ω → RealL2) (p : ℝ≥0×Ω) :
    timeWeight γ t*ENNReal.ofReal (‖raw e hg U t p‖^2)≤
      (ENNReal.ofReal (heatConstant (H : ℝ))*BieleckiKernel.kernel H γ ((t : ℝ)-(p.1 : ℝ)))*
        (timeWeight γ p.1*ScalarLipschitzRawBounds.coeffSquare hg U p) := by
  by_cases hs : p.1<t
  · let r := (t : ℝ)-(p.1 : ℝ)
    have hr : 0<r := sub_pos.mpr (by exact_mod_cast hs)
    have hrH : r≤H := (sub_le_self _ p.1.property).trans (by exact_mod_cast ht)
    have he := kernel_bound e hr hrH (coefficient hg (U p.1 p.2))
    apply (mul_le_mul_right (ENNReal.ofReal_le_ofReal he) _).trans_eq
    rw [timeWeight_factor γ p.1 t,damped_nonzero γ hs ht]
    have hk : 0≤heatConstant (H : ℝ)*r^(-(1/2 : ℝ)) :=
      mul_nonneg (heatConstant_nonneg H.property) (Real.rpow_nonneg hr.le _)
    have hk0 : 0≤heatConstant (H : ℝ) := heatConstant_nonneg H.property
    have hk1 := ENNReal.ofReal_mul (q := r^(-(1/2 : ℝ))) hk0
    rw [ENNReal.ofReal_mul hk,hk1,ENNReal.ofReal_mul (Real.exp_nonneg _),
      ScalarLipschitzRawBounds.coeffSquare]
    dsimp only [r]
    ring
  · rw [raw_zero e hg U t (le_of_not_gt hs),norm_zero]
    simp

end SHEStochastic.ScalarLipschitzDampedEnergy
