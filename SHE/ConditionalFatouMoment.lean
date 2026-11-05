module

public import SHE.RealMomentBound
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ConditionalFatouMoment
open MeasureTheory Filter Topology
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A uniform integral bound passes to an almost-everywhere limit on
any parameter measure. This includes every past-event restriction of
a fixed stochastic measure, with no exceptional set depending on the event. -/
theorem nonnegative_limit (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hlim : ∀ᵐ ω ∂μ,Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hpos : ∀ n ω,0≤f n ω) (hg : ∀ ω,0≤g ω) {K : ℝ} (hK : 0≤K)
    (hb : ∀ n,Integrable (f n) μ ∧ (∫ ω,f n ω ∂μ)≤K) :
    Integrable g μ ∧ (∫ ω,g ω ∂μ)≤K := by
  have hm (n : ℕ) : AEMeasurable (fun ω => ENNReal.ofReal (f n ω)) μ :=
    (hb n).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfat : (∫⁻ ω,Filter.liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂μ)≤
      Filter.liminf (fun n => ∫⁻ ω,ENNReal.ofReal (f n ω) ∂μ) atTop :=
    lintegral_liminf_le' hm
  have he : (fun ω => Filter.liminf (fun n => ENNReal.ofReal (f n ω)) atTop)=ᵐ[μ]
      (fun ω => ENNReal.ofReal (g ω)) := by
    filter_upwards [hlim] with ω hω
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq
  rw [lintegral_congr_ae he] at hfat
  have hb' : Filter.liminf (fun n => ∫⁻ ω,ENNReal.ofReal (f n ω) ∂μ) atTop≤ENNReal.ofReal K :=
    Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently
      (Filter.Eventually.of_forall (fun n => by
        rw [←ofReal_integral_eq_lintegral_ofReal (hb n).1 (ae_of_all _ (hpos n))]
        exact ENNReal.ofReal_le_ofReal (hb n).2)))
  exact RealMomentBound.integral_bound μ g
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hb n).1.aestronglyMeasurable) hlim)
    hg hK (hfat.trans hb')

end SHE.ConditionalFatouMoment
