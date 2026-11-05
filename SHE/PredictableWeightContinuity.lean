module
public import SHE.PredictableWeightedAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.PredictableWeightContinuity
open MeasureTheory PredictableL2 PredictableContraction
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)
variable (a:ℝ≥0×Ω→ℝ)(ha:StronglyMeasurable[𝓕.predictable] a)(hb:∀p,|a p|≤1)

theorem norm_le (u:Process (E:=C) 𝓕 μ H):‖weighted 𝓕 μ H a ha hb u‖≤‖u‖:=by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(weighted_memLp 𝓕 μ H a ha hb u).coeFn_toLp] with p hp
  change weighted 𝓕 μ H a ha hb u p=a p • u p at hp
  rw [hp,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)).trans_eq (one_mul _)

theorem lipschitz:LipschitzWith 1 (weighted (C:=C) 𝓕 μ H a ha hb):=by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  simp only [dist_eq_norm,NNReal.coe_one,one_mul,←PredictableWeightedAlgebra.weighted_sub]
  exact norm_le 𝓕 μ H a ha hb (u-w)

end SHE.PredictableWeightContinuity
