module

public import SHEStochastic.SublinearHeatRows
public import SHEStochastic.HolderWeightedEnergy
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.SublinearHeatCoefficientEnergy
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHEStochastic.SublinearHeatRows AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Actual squared heat-row energy for an unbounded Hölder coefficient.
The right side depends on the L² state norm, with exponent β<1, and
the already proved heat cap. Scalar and finite matrix outputs share it. -/
theorem bound {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β ≤ 1)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖ ^ 2 * ‖G (u x)‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2) *
        (ENNReal.ofReal (cap t) + ENNReal.ofReal (cap t) ^ (1 + (β : ℝ)) *
          ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  let F (x : HeatCircle) := ENNReal.ofReal (‖u x‖ ^ 2)
  let g (x : HeatCircle) := ENNReal.ofReal (‖G (u x)‖ ^ 2)
  let A : ℝ := 2 * (‖G 0‖ + (C : ℝ)) ^ 2
  have hF : AEMeasurable F haarAddCircle := ((Lp.stronglyMeasurable u).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hA : 0 ≤ A := by positivity
  have hg : ∀ᵐ x ∂haarAddCircle, g x ≤ ENNReal.ofReal A * (1 + F x ^ (β : ℝ)) :=
    Filter.Eventually.of_forall (HolderWeightedEnergy.growth hG u)
  have hEn : (∫⁻ x, F x ∂haarAddCircle) = ENNReal.ofReal (‖u‖ ^ 2) :=
    HolderWeightedEnergy.state_mass u
  obtain ⟨hk, hm, hb⟩ := density_properties ht a
  have hh := WeightedSublinearEnergy.with_growth haarAddCircle (density ht a) F g hk.aemeasurable hF
    (ENNReal.ofReal A) (ENNReal.ofReal (cap t)) hb hm β.property (by exact_mod_cast hβ1) hg
  rw [hEn] at hh
  convert hh using 1 <;> simp only [A, density, g, ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _) 2] <;> rfl

/-- Shared coefficient step for any proved heat-cap power bound. Local
and finite-horizon estimates use this same Holder interpolation proof. -/
theorem bound_of_cap_power {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β≤1)
    (u : Lp E 2 (haarAddCircle (T := 2*Real.pi))) {t : ℝ} (ht : 0<t) (a : HeatCircle)
    (K : ℝ) (hcapBound : cap t^(1+(β:ℝ))≤K) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖^2*‖G (u x)‖^2) ∂haarAddCircle)≤
      ENNReal.ofReal (2*(‖G 0‖+(C:ℝ))^2*K)*(1+ENNReal.ofReal (‖u‖^2)^(β:ℝ)) := by
  let A : ℝ := 2*(‖G 0‖+(C:ℝ))^2
  let Q := ENNReal.ofReal (cap t)
  let D := ENNReal.ofReal (‖u‖^2)^(β:ℝ)
  have hA : 0≤A := by positivity
  have hC := heatConstant_pos
  have hcap : 1≤cap t := by
    unfold cap
    exact le_add_of_nonneg_right (by positivity)
  have hp : cap t≤cap t^(1+(β:ℝ)) :=
    (Real.rpow_one (cap t)).symm.trans_le
      (Real.rpow_le_rpow_of_exponent_le hcap (by have := β.property; linarith))
  have hQ : Q≤Q^(1+(β:ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (cap_nonneg ht.le) (by positivity : 0≤1+(β:ℝ))]
    exact ENNReal.ofReal_le_ofReal hp
  have hTime : Q^(1+(β:ℝ))≤ENNReal.ofReal K := by
    rw [ENNReal.ofReal_rpow_of_nonneg (cap_nonneg ht.le) (by positivity : 0≤1+(β:ℝ))]
    exact ENNReal.ofReal_le_ofReal hcapBound
  calc
    _ ≤ ENNReal.ofReal A*(Q+Q^(1+(β:ℝ))*D) := bound hG hβ1 u ht a
    _ ≤ ENNReal.ofReal A*(Q^(1+(β:ℝ))+Q^(1+(β:ℝ))*D) := mul_le_mul_right (add_le_add hQ le_rfl) _
    _ = ENNReal.ofReal A*Q^(1+(β:ℝ))*(1+D) := by ring
    _ ≤ ENNReal.ofReal A*ENNReal.ofReal K*(1+D) := mul_le_mul_left (mul_le_mul_right hTime _) _
    _ = _ := by rw [← ENNReal.ofReal_mul hA]

theorem small_time_bound {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ1 : β ≤ 1)
    (u : Lp E 2 (haarAddCircle (T := 2 * Real.pi))) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (a : HeatCircle) :
    (∫⁻ x, ENNReal.ofReal (‖NativeHeatSpan.kernel t ht a x‖ ^ 2 * ‖G (u x)‖ ^ 2) ∂haarAddCircle) ≤
      ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 *
        ScaledHeatTraceEnvelope.constant 1 2 ^ (1 + (β : ℝ)) * t ^ (-(1 + (β : ℝ)) / 2)) *
          (1 + ENNReal.ofReal (‖u‖ ^ 2) ^ (β : ℝ)) := by
  simpa only [mul_assoc] using bound_of_cap_power hG hβ1 u ht a
    (ScaledHeatTraceEnvelope.constant 1 2^(1+(β:ℝ))*t^(-(1+(β:ℝ))/2))
    (cap_power_bound ht ht1 β.property)

end SHEStochastic.SublinearHeatCoefficientEnergy
