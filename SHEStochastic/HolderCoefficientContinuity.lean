module

public import SHEStochastic.HolderCoefficientIntegrability
public import SHEStochastic.HolderWeightedEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.HolderCoefficientContinuity
open MeasureTheory Filter HolderCoefficientIntegrability
open scoped ENNReal NNReal

variable {X E V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (ν : Measure X) [IsProbabilityMeasure ν]
  {G : E → V} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1) (hG : HolderWith C β G)

/-- Jensen interpolation transfers the coefficient's Holder modulus to
actual L2 classes, for scalar, vector and matrix coefficient values. -/
theorem squared_difference (u v : Lp E 2 ν) :
    ENNReal.ofReal (‖coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v‖ ^ 2) ≤
      ENNReal.ofReal ((C : ℝ) ^ 2) * ENNReal.ofReal (‖u - v‖ ^ 2) ^ (β : ℝ) := by
  let f := fun x ↦ ENNReal.ofReal (‖(u - v : Lp E 2 ν) x‖ ^ 2)
  have hf : AEMeasurable f ν := ((Lp.stronglyMeasurable (u - v)).norm.pow 2).measurable.ennreal_ofReal.aemeasurable
  have hj := WeightedSublinearEnergy.energy_interpolation ν (fun _ ↦ 1) f aemeasurable_const hf 1
    (Eventually.of_forall fun _ ↦ le_rfl) β.property (by exact_mod_cast hβ1)
  simp only [one_mul, lintegral_const, measure_univ, mul_one, ENNReal.one_rpow] at hj
  have hp : ∀ᵐ x ∂ν, ENNReal.ofReal (‖(coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v : Lp V 2 ν) x‖ ^ 2) ≤
      ENNReal.ofReal ((C : ℝ) ^ 2) * f x ^ (β : ℝ) := by
    filter_upwards [Lp.coeFn_sub (coefficient hβ hβ1 hG u) (coefficient hβ hβ1 hG v),
      coefficient_ae hβ hβ1 hG u, coefficient_ae hβ hβ1 hG v, Lp.coeFn_sub u v] with x hs hu hv hd
    change ENNReal.ofReal (‖(coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v) x‖ ^ 2) ≤ _
    rw [hs]
    change ENNReal.ofReal (‖coefficient hβ hβ1 hG u x - coefficient hβ hβ1 hG v x‖ ^ 2) ≤ _
    rw [hu, hv]
    have hh := hG.dist_le (u x) (v x)
    simp only [dist_eq_norm] at hh
    have hb := pow_le_pow_left₀ (norm_nonneg (G (u x) - G (v x))) hh 2
    rw [mul_pow] at hb
    have he : f x ^ (β : ℝ) = ENNReal.ofReal ((‖u x - v x‖ ^ (β : ℝ)) ^ 2) := by
      change ENNReal.ofReal (‖(u - v : Lp E 2 ν) x‖ ^ 2) ^ (β : ℝ) = _
      rw [hd]
      change ENNReal.ofReal (‖u x - v x‖ ^ 2) ^ (β : ℝ) = _
      calc
        _ = ENNReal.ofReal ((‖u x - v x‖ ^ 2) ^ (β : ℝ)) := by
          convert ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ‖u x - v x‖) β.property using 1 <;> rfl
        _ = _ := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul_natCast (norm_nonneg _)]
          congr 1
          ring
    rw [he, ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hb
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖(coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v : Lp V 2 ν) x‖ ^ 2) ∂ν :=
      (HolderWeightedEnergy.state_mass _).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ((C : ℝ) ^ 2) * f x ^ (β : ℝ) ∂ν := lintegral_mono_ae hp
    _ = ENNReal.ofReal ((C : ℝ) ^ 2) * ∫⁻ x, f x ^ (β : ℝ) ∂ν :=
      lintegral_const_mul'' _ (hf.pow_const _)
    _ ≤ _ := by
      have hj' := mul_le_mul_right hj (ENNReal.ofReal ((C : ℝ) ^ 2))
      simp only [f, HolderWeightedEnergy.state_mass] at hj'
      convert hj' using 1 <;> rfl

theorem difference_norm (u v : Lp E 2 ν) :
    ‖coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v‖ ≤
      (C : ℝ) * ‖u - v‖ ^ (β : ℝ) := by
  have hh := ENNReal.toReal_mono
    (by finiteness : ENNReal.ofReal ((C : ℝ) ^ 2) * ENNReal.ofReal (‖u - v‖ ^ 2) ^ (β : ℝ) ≠ ⊤)
    (squared_difference ν hβ hβ1 hG u v)
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sq_nonneg _)] at hh
  have he : (‖u - v‖ ^ 2) ^ (β : ℝ) = (‖u - v‖ ^ (β : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2 (β : ℝ),
      ← Real.rpow_mul_natCast (norm_nonneg _) (β : ℝ) 2]
    congr 1
    ring
  rw [he] at hh
  have hc := C.property
  have hp := Real.rpow_nonneg (norm_nonneg (u - v)) (β : ℝ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc hp)).mp
  exact hh.trans_eq (mul_pow _ _ 2).symm

theorem holder : HolderWith C β (coefficient hβ hβ1 hG (ν := ν)) := by
  intro u v
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
  have he := ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (u - v)) β.property
  change ENNReal.ofReal ‖coefficient hβ hβ1 hG u - coefficient hβ hβ1 hG v‖ ≤ _
  have hh := ENNReal.ofReal_le_ofReal (difference_norm ν hβ hβ1 hG u v)
  have hpow : ENNReal.ofReal ‖u - v‖ ^ (β : ℝ) = ENNReal.ofReal (‖u - v‖ ^ (β : ℝ)) := by
    convert he using 1 <;> rfl
  rw [hpow]
  have hprod := ENNReal.ofReal_mul (q := ‖u - v‖ ^ (β : ℝ)) C.property
  exact hh.trans_eq (by
    calc
      _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (‖u - v‖ ^ (β : ℝ)) := by
        convert hprod using 1 <;> rfl
      _ = _ := congrArg (fun z : ℝ≥0∞ ↦ z * ENNReal.ofReal (‖u - v‖ ^ (β : ℝ)))
        ENNReal.ofReal_coe_nnreal)

theorem continuous : Continuous (coefficient hβ hβ1 hG (ν := ν)) :=
  (holder ν hβ hβ1 hG).continuous hβ

end SHEStochastic.HolderCoefficientContinuity
