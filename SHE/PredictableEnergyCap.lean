module
public import SHE.CumulativeEnergyCap
public import SHE.ContinuousPredictable
public import SHE.PredictableTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.PredictableEnergyCap
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(U:ℝ≥0→Ω→E)

def realEnergy(ω:Ω)(r:ℝ):ℝ:=‖U r.toNNReal ω‖^2

def accumulated(t:ℝ≥0)(ω:Ω):ℝ:=CumulativeEnergyCap.cumulative (realEnergy U ω) (t:ℝ)

def capped(t:ℝ≥0)(ω:Ω):E:=if accumulated U t ω<1 then U t ω else 0

theorem continuous_energy(hc:∀ω,Continuous (fun t=>U t ω))(ω:Ω):Continuous (realEnergy U ω):=
  ((hc ω).comp continuous_real_toNNReal).norm.pow 2

theorem accumulated_continuous(hc:∀ω,Continuous (fun t=>U t ω))(ω:Ω):
    Continuous (fun t=>accumulated U t ω):=
  (CumulativeEnergyCap.continuous_cumulative (continuous_energy U hc ω)).comp continuous_subtype_val

/-- The accumulated control cost at t is measurable in the ORIGINAL
past sigma algebra F_t; no future path or stopping witness is used. -/
theorem accumulated_adapted(ha:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun t=>U t ω)):
    StronglyAdapted 𝓕 (accumulated U):=by
  intro t
  letI:MeasurableSpace Ω:=𝓕 t
  let F:ℝ→Ω→ℝ:=fun r ω=>‖U (min r.toNNReal t) ω‖^2
  have hFc:∀ω,Continuous (fun r=>F r ω):=by
    intro ω
    exact ((hc ω).comp (continuous_real_toNNReal.min continuous_const)).norm.pow 2
  have hFm:∀r,StronglyMeasurable (F r):=by
    intro r
    exact (((ha (min r.toNNReal t)).mono (𝓕.mono (min_le_right _ _))).norm.pow 2)
  have hj:=stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hFc hFm
  have hi:StronglyMeasurable (fun ω=>∫r,F r ω ∂volume.restrict (Ioc (0:ℝ) (t:ℝ))):=
    hj.integral_prod_left
  convert! hi using 1
  funext ω
  unfold accumulated CumulativeEnergyCap.cumulative
  have he:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ)) (f:=realEnergy U ω) t.2
  trans (∫r,realEnergy U ω r ∂volume.restrict (Ioc (0:ℝ) (t:ℝ)))
  · convert! he using 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hrt:r.toNNReal≤t:=by
    exact_mod_cast (show (r.toNNReal:ℝ)≤(t:ℝ) from by rw [Real.coe_toNNReal _ hr.1.le];exact hr.2)
  simp only [F,min_eq_left hrt,realEnergy]

/-- The energy-threshold cut is a genuine original predictable field. -/
theorem predictable(ha:StronglyAdapted 𝓕 U)(hc:∀ω,Continuous (fun t=>U t ω)):
    StronglyMeasurable[𝓕.predictable] (Function.uncurry (capped U)):=by
  have hu:=ContinuousPredictable.stronglyMeasurable 𝓕 U ha hc
  have ha:=ContinuousPredictable.stronglyMeasurable 𝓕 (accumulated U)
    (accumulated_adapted 𝓕 U ha hc) (accumulated_continuous U hc)
  have hs:MeasurableSet[𝓕.predictable] {p:ℝ≥0×Ω|accumulated U p.1 p.2<1}:=
    measurableSet_lt ha.measurable measurable_const
  convert! hu.indicator hs using 1

theorem norm_sq(hc:∀ω,Continuous (fun t=>U t ω))(ω:Ω)(t:ℝ≥0):
    ‖capped U t ω‖^2=CumulativeEnergyCap.clipped (realEnergy U ω) (t:ℝ):=by
  simp only [capped,CumulativeEnergyCap.clipped,accumulated,realEnergy,Real.toNNReal_coe]
  split_ifs <;> simp

/-- The true time energy of every capped control path is at most one. -/
theorem path_energy(hc:∀ω,Continuous (fun t=>U t ω))(H:ℝ≥0)(ω:Ω):
    (∫t,‖capped U t ω‖^2 ∂timeMeasure H)≤1:=by
  rw [timeMeasure_integral]
  have hh:=CumulativeEnergyCap.energy_le_one (continuous_energy U hc ω)
    (fun r=>sq_nonneg ‖U r.toNNReal ω‖) H.2
  apply le_trans (a:=∫r,‖capped U r.toNNReal ω‖^2 ∂volume.restrict (Ioc 0 (H:ℝ))) (b:=∫r,CumulativeEnergyCap.clipped (realEnergy U ω) r ∂volume.restrict (Ioc 0 (H:ℝ))) ?_ hh.2
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [norm_sq U hc ω r.toNNReal,Real.coe_toNNReal _ hr.1.le]

theorem no_exit(hc:∀ω,Continuous (fun t=>U t ω))(H:ℝ≥0)(ω:Ω)
    (hcost:accumulated U H ω<1)(t:ℝ≥0)(ht:t≤H):capped U t ω=U t ω:=by
  have hm:=CumulativeEnergyCap.monotone_cumulative (continuous_energy U hc ω)
    (fun r=>sq_nonneg ‖U r.toNNReal ω‖) t.2 H.2 (show (t:ℝ)≤(H:ℝ) by exact_mod_cast ht)
  exact if_pos (hm.trans_lt hcost)
end SHE.PredictableEnergyCap
