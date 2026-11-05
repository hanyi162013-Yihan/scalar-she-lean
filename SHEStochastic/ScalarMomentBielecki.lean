module

public import SHE.BieleckiColumnEnergy
public import SHE.TimeMeasureMass

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarMomentBielecki
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal

/-- An actual causal inequality with the square-root heat kernel
bounds integrated state energy independently of the preliminary
localization cap. The coefficient and horizon choose the damping. -/
theorem bound (H : ℝ≥0) (A B : ℝ) (hA : 0≤A) (hB : 0≤B) :
    ∃ C : ℝ,0≤C ∧
      ∀ (f : ℝ≥0 → ℝ≥0∞) (M : ℝ≥0), Measurable f → (∀ t,f t≤M) →
      (∀ᵐ t ∂PredictableL2.timeMeasure H,
        f t≤ENNReal.ofReal A+ENNReal.ofReal B*
          (∫⁻ s,ENNReal.ofReal (((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ)))*f s ∂PredictableL2.timeMeasure t)) →
      (∫⁻ t,f t ∂PredictableL2.timeMeasure H)≤ENNReal.ofReal C := by
  obtain ⟨γ,hγ,hsmall⟩ := BieleckiKernel.exists_contraction_weight B
  have hγ' : 0<γ := zero_lt_one.trans_le hγ
  refine ⟨Real.exp (2*γ*(H : ℝ))*(2*A*(H : ℝ)),by positivity,?_⟩
  intro f M hf hM hVol
  let w (t : ℝ≥0) := ENNReal.ofReal (Real.exp (-2*γ*(t : ℝ)))
  let F (t : ℝ≥0) := w t*f t
  have hw : Measurable w := by unfold w; fun_prop
  have hF : Measurable F := hw.mul hf
  have hw₁ (t : ℝ≥0) : w t≤1 := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr (by
      have ht : 0≤(t : ℝ) := t.property
      nlinarith))
  have hD : ∀ᵐ t ∂PredictableL2.timeMeasure H,
      F t≤ENNReal.ofReal A+ENNReal.ofReal B*
        (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*F s ∂PredictableL2.timeMeasure t) := by
    filter_upwards [hVol,timeMeasure_ae_mem H] with t ht htime
    have he : w t*(∫⁻ s,ENNReal.ofReal (((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ)))*f s ∂PredictableL2.timeMeasure t) =
        ∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*F s ∂PredictableL2.timeMeasure t := by
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [timeMeasure_ae_mem t,(PredictableL2.timeMeasure t).ae_ne t] with s hs hst
      have hpos : 0<(t : ℝ)-(s : ℝ) := sub_pos.mpr (by exact_mod_cast lt_of_le_of_ne hs.2 hst)
      have hle : (t : ℝ)-(s : ℝ)≤H := (sub_le_self _ s.property).trans (by exact_mod_cast htime.2)
      rw [BieleckiKernel.kernel,Set.indicator_of_mem (show (t : ℝ)-(s : ℝ) ∈ Ioc 0 (H : ℝ) from ⟨hpos,hle⟩)]
      dsimp only [F,w]
      rw [←mul_assoc,←mul_assoc,←ENNReal.ofReal_mul (Real.exp_nonneg _),
        ←ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hpos.le _))]
      congr 2
      have hd : Real.exp (-2*γ*(t : ℝ)) =
          Real.exp (-2*γ*((t : ℝ)-(s : ℝ)))*Real.exp (-2*γ*(s : ℝ)) := by
        rw [←Real.exp_add]
        congr 1
        ring
      rw [hd]
      ring
    calc
      F t ≤ w t*(ENNReal.ofReal A+ENNReal.ofReal B*
          ∫⁻ s,ENNReal.ofReal (((t : ℝ)-(s : ℝ))^(-(1/2 : ℝ)))*f s ∂PredictableL2.timeMeasure t) :=
        mul_le_mul_right ht _
      _ = w t*ENNReal.ofReal A+ENNReal.ofReal B*
          (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*F s ∂PredictableL2.timeMeasure t) := by
        rw [mul_add,←he,mul_left_comm (w t)]
      _ ≤ _ := add_le_add (calc
          w t*ENNReal.ofReal A ≤ 1*ENNReal.ofReal A := by gcongr; exact hw₁ t
          _ = _ := one_mul _) le_rfl
  let R := ∫⁻ t,F t ∂PredictableL2.timeMeasure H
  have hfin : R≠⊤ := by
    apply ne_top_of_le_ne_top (b := (M : ℝ≥0∞)*ENNReal.ofReal (H : ℝ)) (by finiteness)
    rw [←timeMeasure_mass,←lintegral_const]
    apply lintegral_mono
    intro t
    change w t*f t≤M
    calc
      _ ≤ 1*(M : ℝ≥0∞) := mul_le_mul (hw₁ t) (hM t) bot_le bot_le
      _ = _ := one_mul _
  have hInt : R≤ENNReal.ofReal (A*(H : ℝ))+ENNReal.ofReal (B*BieleckiKernel.mass γ)*R := by
    calc
      _ ≤ ∫⁻ t,ENNReal.ofReal A+ENNReal.ofReal B*
          (∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*F s ∂PredictableL2.timeMeasure t)
          ∂PredictableL2.timeMeasure H := lintegral_mono_ae hD
      _ = ENNReal.ofReal (A*(H : ℝ))+ENNReal.ofReal B*
          (∫⁻ t,∫⁻ s,BieleckiKernel.kernel H γ ((t : ℝ)-(s : ℝ))*F s ∂PredictableL2.timeMeasure t
            ∂PredictableL2.timeMeasure H) := by
        rw [lintegral_add_left measurable_const,lintegral_const,timeMeasure_mass,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.ofReal_mul hA]
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul hB,mul_assoc]
        gcongr
        exact BieleckiColumnEnergy.causal_energy H hγ' F hF
  have hcoeff : 0≤B*BieleckiKernel.mass γ :=
    mul_nonneg hB (BieleckiKernel.mass_nonneg hγ'.le)
  have hr := ENNReal.toReal_mono (by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin⟩) hInt
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin),
    ENNReal.toReal_mul] at hr
  have hAr : (ENNReal.ofReal (A*(H : ℝ))).toReal=A*(H : ℝ) :=
    ENNReal.toReal_ofReal (mul_nonneg hA (show (0 : ℝ)≤H from H.property))
  have hBr : (ENNReal.ofReal (B*BieleckiKernel.mass γ)).toReal=B*BieleckiKernel.mass γ :=
    ENNReal.toReal_ofReal hcoeff
  rw [hAr,hBr] at hr
  have hR : R≤ENNReal.ofReal (2*A*(H : ℝ)) := by
    rw [←ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_right hsmall (ENNReal.toReal_nonneg (a := R))])
  calc
    _ ≤ ∫⁻ t,ENNReal.ofReal (Real.exp (2*γ*(H : ℝ)))*F t ∂PredictableL2.timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem H] with t ht
      have he : ENNReal.ofReal (Real.exp (2*γ*(t : ℝ)))*w t=1 := by
        unfold w
        rw [←ENNReal.ofReal_mul (Real.exp_nonneg _),←Real.exp_add]
        rw [show 2*γ*(t : ℝ)+(-2)*γ*(t : ℝ)=0 by ring,Real.exp_zero,ENNReal.ofReal_one]
      have hle : Real.exp (2*γ*(t : ℝ))≤Real.exp (2*γ*(H : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast ht.2) (by positivity))
      calc
        f t = ENNReal.ofReal (Real.exp (2*γ*(t : ℝ)))*F t := by
          change f t = ENNReal.ofReal (Real.exp (2*γ*(t : ℝ)))*(w t*f t)
          rw [←mul_assoc,he,one_mul]
        _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hle) _
    _ ≤ _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,ENNReal.ofReal_mul (Real.exp_nonneg _)]
      exact mul_le_mul_right hR _

end SHEStochastic.ScalarMomentBielecki
