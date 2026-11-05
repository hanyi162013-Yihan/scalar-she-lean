module
public import SHE.StoppedComparison
public import SHE.StandardTerminalIto
public import SHE.PredictableTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.StochasticExponential
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

def bracket(u:Process (E:=C) 𝓕 μ H)(ω:Ω):ℝ:=∫t,‖u (t,ω)‖^2 ∂timeMeasure H

def density(J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)(u:Process (E:=C) 𝓕 μ H)(ω:Ω):ℝ:=
  Real.exp (-J.integral u ω-bracket 𝓕 μ H u ω/2)

theorem bracket_measurable(u:Process (E:=C) 𝓕 μ H):Measurable (bracket 𝓕 μ H u):=by
  have hm:=((Lp.stronglyMeasurable u).mono (predictable_le_product 𝓕)).norm.pow 2
  exact hm.integral_prod_left.measurable

theorem bracket_integrable[SFinite μ](u:Process (E:=C) 𝓕 μ H):Integrable (bracket 𝓕 μ H u) μ:=by
  have hi:Integrable (fun p:ℝ≥0×Ω=>‖u p‖^2) (energyMeasure μ H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp u)).norm.integrable_sq
  exact hi.integral_prod_right

theorem expected_bracket[SFinite μ](u:Process (E:=C) 𝓕 μ H):
    (∫ω,bracket 𝓕 μ H u ω ∂μ)=‖u‖^2:=by
  have hi:Integrable (fun p:ℝ≥0×Ω=>‖u p‖^2) (energyMeasure μ H):=
    (memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp u)).norm.integrable_sq
  unfold bracket
  rw [←integral_prod_symm _ hi]
  exact (subsigma_norm_sq (energyMeasure μ H) (predictable_le_product 𝓕) u).symm
end SHE.StochasticExponential

namespace SHE
open MeasureTheory PredictableL2
open scoped NNReal
/-- Accepted external package6, ordinary Novikov mean-one theorem for
an actual predictable Hilbert Ito integral. Heat estimates, bounded
control energy and canonical solution laws are NOT part of this input. -/
def StandardTerminalNovikov {Ω C:Type*}[MeasurableSpace Ω]
    [NormedAddCommGroup C][InnerProductSpace ℝ C]
    {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}{H:ℝ≥0}
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H):Prop:=
  ∀u:Process (E:=C) 𝓕 μ H,
    Integrable (fun ω=>Real.exp (StochasticExponential.bracket 𝓕 μ H u ω/2)) μ→
      Integrable (StochasticExponential.density 𝓕 μ H J u) μ ∧
        (∫ω,StochasticExponential.density 𝓕 μ H J u ω ∂μ)=1
end SHE

namespace SHE.StochasticExponential
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω][NormedAddCommGroup C][InnerProductSpace ℝ C]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)

theorem mean_one_of_cap(hNovikov:StandardTerminalNovikov J)(u:Process (E:=C) 𝓕 μ H)
    (hcap:∀ᵐω∂μ,bracket 𝓕 μ H u ω≤1):
    Integrable (density 𝓕 μ H J u) μ ∧ (∫ω,density 𝓕 μ H J u ω ∂μ)=1:=by
  apply hNovikov u
  apply Integrable.of_bound (((bracket_measurable 𝓕 μ H u).div_const 2).exp).aestronglyMeasurable (Real.exp (1/2:ℝ))
  filter_upwards [hcap] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Exact actual reverse entropy; only ordinary centering is used in
this algebraic consequence, not the Novikov theorem. -/
theorem entropy(u:Process (E:=C) 𝓕 μ H):
    Integrable (fun ω=>Real.log (density 𝓕 μ H J u ω)) μ ∧
      -(∫ω,Real.log (density 𝓕 μ H J u ω) ∂μ)=‖u‖^2/2:=by
  have hi:Integrable (fun ω=>J.integral u ω) μ:=(Lp.memLp (J.integral u)).integrable (by norm_num)
  have hh:=exponential_entropy_identity μ hi (bracket_integrable 𝓕 μ H u) (J.centered u)
  simpa only [density,expected_bracket 𝓕 μ H u] using hh
end SHE.StochasticExponential
