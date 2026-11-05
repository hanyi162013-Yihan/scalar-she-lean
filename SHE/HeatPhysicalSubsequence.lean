module

public import SHE.HeatFieldWeightedLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.HeatPhysicalSubsequence
open Set MeasureTheory AddCircle StoppedFourier NativeHeatObservation Filter Topology
open DyadicApproximation HeatFieldApproximation HeatFieldWeightedLimit
local instance heatPhysicalSubsequence_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance heatPhysicalSubsequence_realSigma : MeasurableSpace RealL2 := borel _
local instance heatPhysicalSubsequence_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

theorem arctan_bound (z : ℝ) : |Real.arctan z| ≤ Real.pi/2 := by
  exact (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan z).le,(Real.arctan_lt_pi_div_two z).le⟩)

theorem arctan_lipschitz : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro z
  rw [Real.deriv_arctan]
  change |1/(1+z^2)| ≤ (1:ℝ)
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity : 0<1+z^2)).2 (by nlinarith [sq_nonneg z])

/-- Bounded arctangent coordinates remove any energy assumption on a measurable
family of L² states. Their heat regularizations converge in measure on the
actual parameter-space × physical-circle product. -/
theorem arctan_tendstoInMeasure (U : P → RealL2) (hU : Measurable U)
    (ν : Measure P) [IsFiniteMeasure ν] :
    TendstoInMeasure (ν.prod (haarAddCircle (T:=2*Real.pi)))
      (fun ε (p : P × HeatCircle) => Real.arctan
        (PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε,p.2)))
      (𝓝[>] (0:ℝ))
      (fun p => Real.arctan (PredictableScalarField.nativeField U p)) := by
  have hLip (z w : ℝ) : |Real.arctan z-Real.arctan w| ≤ 1*|z-w| := by
    simpa only [Real.dist_eq,NNReal.coe_one] using arctan_lipschitz.dist_le_mul z w
  have ht := integrated_mass_tendsto_zero U hU Real.arctan Real.continuous_arctan.measurable
    (fun _ : P × HeatCircle => (1:ℝ)) measurable_const ν arctan_bound (by norm_num : 0≤(1:ℝ))
    (fun _ => by norm_num) (by norm_num : 0≤(1:ℝ)) hLip
  have hi (ε : ℝ) : Integrable (difference U Real.arctan ε)
      (ν.prod (haarAddCircle (T:=2*Real.pi))) := by
    apply (integrable_const Real.pi).mono'
      (difference_measurable U hU Real.arctan Real.continuous_arctan.measurable ε).aestronglyMeasurable
    filter_upwards with p
    change |Real.arctan _-Real.arctan _| ≤ Real.pi
    exact (abs_sub _ _).trans ((add_le_add (arctan_bound _) (arctan_bound _)).trans_eq (by ring))
  have he (ε : ℝ) : eLpNorm (difference U Real.arctan ε) 1
      (ν.prod (haarAddCircle (T:=2*Real.pi))) =
      ENNReal.ofReal (∫ p,mass U Real.arctan (fun _ => (1:ℝ)) ε p ∂ν) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi ε).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi ε),integral_prod _ (hi ε).norm]
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    simp only [mass,mul_one,Real.norm_eq_abs]
  have hn : Tendsto (fun ε => eLpNorm (difference U Real.arctan ε) 1
      (ν.prod (haarAddCircle (T:=2*Real.pi)))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [he,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp ht
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1:ENNReal)≠0) hn

/-- A single spatial exceptional set works for every restriction of the
parameter measure. No integrability of the unbounded field is required. -/
theorem exists_subsequence (U : P → RealL2) (hU : Measurable U)
    (ν : Measure P) [IsFiniteMeasure ν] (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝[>] (0:ℝ))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ p ∂(ν.prod (haarAddCircle (T:=2*Real.pi))),
        Tendsto (fun n => PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε (ns n),p.2))
          atTop (𝓝 (PredictableScalarField.nativeField U p)) := by
  obtain ⟨ns,hns,hae⟩ := ((arctan_tendstoInMeasure U hU ν).comp hε).exists_seq_tendsto_ae
  refine ⟨ns,hns,hae.mono (fun p hp => ?_)⟩
  have hc := (Real.continuousAt_tan.2 (Real.cos_arctan_pos
    (PredictableScalarField.nativeField U p)).ne').tendsto.comp hp
  simpa only [Function.comp_def,Real.tan_arctan] using hc

/-- The same positive heat ages realize two arbitrary measurable state
families on a single product-measure event. -/
theorem exists_common_subsequence (U V : P → RealL2) (hU : Measurable U) (hV : Measurable V)
    (ν : Measure P) [IsFiniteMeasure ν] :
    ∃ ε : ℕ → ℝ, (∀ n,0<ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᵐ p ∂(ν.prod (haarAddCircle (T:=2*Real.pi))),
        Tendsto (fun n => PhysicalProfile.physicalHeatMean (embed (U p.1)) (ε n,p.2))
          atTop (𝓝 (PredictableScalarField.nativeField U p)) ∧
        Tendsto (fun n => PhysicalProfile.physicalHeatMean (embed (V p.1)) (ε n,p.2))
          atTop (𝓝 (PredictableScalarField.nativeField V p)) := by
  let rate : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0<rate n := by dsimp only [rate]; positivity
  have ht : Tendsto rate atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Filter.Eventually.of_forall hr⟩
  obtain ⟨ns,hns,hUlim⟩ := exists_subsequence U hU ν rate ht
  obtain ⟨ms,hms,hVlim⟩ := exists_subsequence V hV ν (fun n => rate (ns n))
    (ht.comp hns.tendsto_atTop)
  refine ⟨fun n => rate (ns (ms n)),fun n => hr _,
    ((ht.comp hns.tendsto_atTop).comp hms.tendsto_atTop).mono_right inf_le_left,?_⟩
  filter_upwards [hUlim,hVlim] with p hu hv
  exact ⟨hu.comp hms.tendsto_atTop,hv⟩

end SHE.HeatPhysicalSubsequence
