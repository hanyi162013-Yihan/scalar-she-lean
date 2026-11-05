module

public import SHE.PastItoAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.PastItoContinuity
open Set MeasureTheory PredictableL2 PastItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [NormedSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H v : ℝ≥0)

theorem norm_le (u : Process (E:=C) 𝓕 μ H) : ‖post 𝓕 μ H v u‖≤‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have he : post 𝓕 μ H v u=ᵐ[(energyMeasure μ H).trim (predictable_le_product 𝓕)]
      (fun p=>if v<p.1 then u p else 0) := by
    apply ae_eq_trim_of_measurable (predictable_le_product 𝓕) (Lp.stronglyMeasurable _).measurable
    · exact (Lp.stronglyMeasurable u).measurable.ite
        (measurableSet_lt measurable_const (PredictableClock.time_measurable 𝓕)) measurable_const
    · exact post_ae 𝓕 μ H v u
  filter_upwards [he] with p hp
  rw [hp]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (u p)

theorem lipschitz : LipschitzWith 1 (post (C:=C) 𝓕 μ H v) := by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  simp only [dist_eq_norm,NNReal.coe_one,one_mul,←PastItoAlgebra.post_sub]
  exact norm_le 𝓕 μ H v (u-w)

end SHE.PastItoContinuity
