module

public import SHE.VariableFiniteMarkFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section
namespace SHE.VariableScoreMassFields
open Set MeasureTheory ProbabilityTheory Real AddCircle GaussianIncrement StoppedFourier StoppedGaussianFeatures
local instance : Fact (0<2*π):=⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse
variable {W:Type} [MeasurableSpace W] {n:ℕ}

/-- The actual signed-input leverage mass is Borel through moving history
cutoffs, changing-rank covariance and arbitrary dependent physical rows. -/
theorem history_mass_measurable
    (A:W→Matrix (Fin n) (Fin n) ℝ) (hA:Measurable A)
    (row:W×Domain→State n) (hrow:Measurable row) (e:W×Domain→ℝ) (he:Measurable e)
    (q:W→ℝ) (hq:Measurable q):
    Measurable (fun w=>∫z,|e (w,z)| *MeasurableGaussianScores.scoreVariance (A w) (row (w,z))
      ∂historyMeasure (q w)):=by
  have hS:Measurable (fun z:W×Domain=>MeasurableGaussianScores.scoreVariance (A z.1) (row z)):=
    MeasurableGaussianScores.scoreVariance_measurable.comp ((hA.comp measurable_fst).prodMk hrow)
  have hset:MeasurableSet {z:W×Domain | q z.1≤z.2.1}:=
    measurableSet_le (hq.comp measurable_fst) measurable_snd.fst
  have hh:Measurable (fun z:W×Domain=>if q z.1≤z.2.1 then
      |e z| *MeasurableGaussianScores.scoreVariance (A z.1) (row z) else 0):=
    ((continuous_abs.measurable.comp he).mul hS).ite hset measurable_const
  have hi:=(hh.stronglyMeasurable.integral_prod_right'
    (ν:=volume.prod (haarAddCircle (T:=2*π)))).measurable
  convert! hi using 1
  funext w
  unfold historyMeasure
  rw [Measure.restrict_prod_eq_prod_univ,←integral_indicator
    (measurableSet_Ici.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Set.indicator,mem_prod,mem_Ici,mem_univ,and_true]

end SHE.VariableScoreMassFields
