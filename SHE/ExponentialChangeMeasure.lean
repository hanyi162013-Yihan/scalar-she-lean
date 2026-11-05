module
public import SHE.CappedStochasticExponential
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ExponentialChangeMeasure
open MeasureTheory
open scoped ENNReal
variable {Ω:Type*}[MeasurableSpace Ω](μ:Measure Ω)(W V:Ω→ℝ)

def measure:Measure Ω:=μ.withDensity (fun ω=>ENNReal.ofReal (Real.exp (-W ω-V ω/2)))

/-- The actual mean-one exponential defines a probability measure. -/
theorem probability (hi:Integrable (fun ω=>Real.exp (-W ω-V ω/2)) μ)
    (hmean:(∫ω,Real.exp (-W ω-V ω/2) ∂μ)=1):IsProbabilityMeasure (measure μ W V):=by
  constructor
  rw [measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun ω=>(Real.exp_pos _).le)),hmean]
  simp

/-- Strict positivity gives equivalence of null sets on the ORIGINAL
space; no changed-space canonical solution law is assumed. -/
theorem original_absolutelyContinuous
    (hi:Integrable (fun ω=>Real.exp (-W ω-V ω/2)) μ):μ ≪ measure μ W V:=by
  apply withDensity_absolutelyContinuous' hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  exact ae_of_all _ (fun ω=>ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))

theorem changed_absolutelyContinuous:measure μ W V ≪ μ:=
  withDensity_absolutelyContinuous μ _

theorem ae_eq_iff {F:Type*}(f g:Ω→F)
    (hi:Integrable (fun ω=>Real.exp (-W ω-V ω/2)) μ):
    f=ᵐ[measure μ W V] g ↔ f=ᵐ[μ] g:=by
  exact withDensity_ae_eq hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun ω=>ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))

end SHE.ExponentialChangeMeasure
