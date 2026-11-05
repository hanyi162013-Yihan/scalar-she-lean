module

public import SHE.PredictableExponential
public import SHE.BieleckiKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.PredictableBieleckiFixedPoint
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- A heat-kernel weighted energy estimate constructs the forced fixed
point on any fixed finite horizon, for an arbitrary Hilbert target. -/
theorem exists_unique (N : Process (E := E) F μ H → Process (E := E) F μ H)
    (C : ℝ) (hC : 0 ≤ C)
    (hEnergy : ∀ γ : ℝ, 0 < γ → ∀ u v,
      ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (N u-N v)‖^2) ≤
        ENNReal.ofReal (C*BieleckiKernel.mass γ)*
          ENNReal.ofReal (‖PredictableExponential.scale F μ H (-γ) (u-v)‖^2))
    (forcing : Process (E := E) F μ H) :
    ∃! v : Process (E := E) F μ H, v=forcing+N v := by
  obtain ⟨γ,hγ,hs⟩ := BieleckiKernel.exists_contraction_weight C
  have hγpos : 0 < γ := zero_lt_one.trans_le hγ
  apply PredictableExponential.exists_unique F μ H γ forcing N
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he := hEnergy γ hγpos (PredictableExponential.scale F μ H γ u)
    (PredictableExponential.scale F μ H γ v)
  rw [← PredictableExponential.sub,PredictableExponential.cancel] at he
  have hCm := mul_nonneg hC (BieleckiKernel.mass_nonneg hγpos.le)
  rw [← ENNReal.ofReal_mul hCm] at he
  have hr := ((ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCm (sq_nonneg ‖u-v‖))).mp he).trans
    (mul_le_mul_of_nonneg_right hs (sq_nonneg ‖u-v‖))
  have hd : PredictableExponential.conjugate F μ H γ forcing N u-
      PredictableExponential.conjugate F μ H γ forcing N v=
      PredictableExponential.scale F μ H (-γ)
        (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v)) := by
    rw [PredictableExponential.conjugate,PredictableExponential.conjugate,
      ← PredictableExponential.sub,add_sub_add_left_eq_sub]
  rw [dist_eq_norm,dist_eq_norm,hd]
  change ‖PredictableExponential.scale F μ H (-γ)
    (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v))‖ ≤
      (1/2 : ℝ)*‖u-v‖
  nlinarith [norm_nonneg (PredictableExponential.scale F μ H (-γ)
    (N (PredictableExponential.scale F μ H γ u)-N (PredictableExponential.scale F μ H γ v))),
    norm_nonneg (u-v)]

end SHEStochastic.PredictableBieleckiFixedPoint
