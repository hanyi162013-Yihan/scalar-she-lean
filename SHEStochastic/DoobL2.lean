module

public import SHEStochastic.MaximalL2
public import BrownianMotion.StochasticIntegral.DoobLp
public import Mathlib.Analysis.Convex.Mul

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.DoobL2
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology

variable {ι Ω : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]
  [SecondCountableTopology ι] [MeasurableSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {𝓕 : Filtration ι ‹MeasurableSpace Ω›}
  {Y : ι → Ω → ℝ}

/-- Doob's strong L² inequality for a nonnegative right-continuous
submartingale, derived from the verified weak maximal inequality. -/
theorem submartingale (hsub : Submartingale Y 𝓕 μ) (hn : 0 ≤ Y)
    (hc : ∀ ω, IsRightContinuous (Y · ω)) (T : ι) (hy : MemLp (Y T) 2 μ) :
    (∫⁻ ω, (⨆ t : Set.Iic T, ENNReal.ofReal (Y t ω)) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (Y T ω ^ 2) ∂μ := by
  let M (ω : Ω) := ⨆ t : Set.Iic T, ENNReal.ofReal (Y t ω)
  let S (ω : Ω) := (M ω).toReal
  have hYm (t : ι) : Measurable (Y t) :=
    (hsub.stronglyMeasurable t).measurable.mono (𝓕.le t) le_rfl
  have hM : Measurable M := by
    have heq : M = ⨆ t : Set.Iic T, (fun ω => ENNReal.ofReal (Y t ω)) := by ext; simp [M]
    rw [heq]
    refine measurable_iSup_of_rightContinuous (fun ω => ?_) (fun t => (hYm t).ennreal_ofReal)
    refine fun a => ((hc ω).continuous_comp ENNReal.continuous_ofReal a).comp ?_ ?_
    · exact continuous_subtype_val.continuousWithinAt
    · exact fun x => by simp
  have hfinite : ∀ᵐ ω ∂μ, M ω ≠ ∞ := hsub.rightCont_iSup_ofReal_ne_top hn T hc
  have hweak : MaximalL2.WeakBound μ S (Y T) := by
    intro t ht
    let A := {ω | ENNReal.ofReal t ≤ M ω}
    have hA : MeasurableSet A := measurableSet_le measurable_const hM
    have hraw : t * μ.real A ≤ ∫ ω in A, Y T ω ∂μ := by
      simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal t ht.le, M, A] using
        maximal_ineq_ennreal hsub hn t.toNNReal T hc
    have h := ENNReal.ofReal_le_ofReal hraw
    have hmeasure : ENNReal.ofReal (μ.real A) = μ A :=
      ENNReal.ofReal_toReal (measure_ne_top μ A)
    rw [ENNReal.ofReal_mul ht.le, hmeasure,
      ofReal_integral_eq_lintegral_ofReal (hsub.integrable T).integrableOn
        (Filter.Eventually.of_forall (fun ω => hn T ω))] at h
    have hset : {ω | t ≤ S ω} =ᵐ[μ] A := by
      filter_upwards [hfinite] with ω hω
      apply propext
      change (t ≤ S ω) ↔ ENNReal.ofReal t ≤ M ω
      have he : M ω = ENNReal.ofReal (S ω) := (ENNReal.ofReal_toReal hω).symm
      rw [he]
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).symm
    rw [measure_congr hset, Measure.restrict_congr_set hset]
    exact h
  have hb := MaximalL2.lintegral_bound μ hM.ennreal_toReal (hYm T)
    (fun _ => ENNReal.toReal_nonneg) (hn T) hy hweak
  have he : (∫⁻ ω, M ω ^ 2 ∂μ) = ∫⁻ ω, ENNReal.ofReal (S ω ^ 2) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfinite] with ω hω
    calc
      _ = (ENNReal.ofReal (S ω)) ^ 2 := congrArg (fun r : ℝ≥0∞ => r ^ 2)
        (ENNReal.ofReal_toReal hω).symm
      _ = _ := (ENNReal.ofReal_pow ENNReal.toReal_nonneg 2).symm
  exact he.trans_le hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → Ω → E}

/-- The strong maximal inequality applies to Hilbert/Banach-valued
martingales through the already proved norm submartingale theorem. -/
theorem martingale (hmar : Martingale X 𝓕 μ)
    (hc : ∀ ω, IsRightContinuous (X · ω)) (T : ι) (hy : MemLp (X T) 2 μ) :
    (∫⁻ ω, (⨆ t : Set.Iic T, ‖X t ω‖ₑ) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ‖X T ω‖ₑ ^ 2 ∂μ := by
  have h := submartingale hmar.submartingale_norm (fun _ _ => norm_nonneg _)
    (fun ω => (hc ω).continuous_comp continuous_norm) T hy.norm
  simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using h

/-- Applying Doob L² to a convex norm power gives the maximal estimate
needed at every even moment. The constant 4 suffices for our purposes. -/
theorem martingale_norm_power (hmar : Martingale X 𝓕 μ)
    (hc : ∀ ω, IsRightContinuous (X · ω)) (p : ℕ) (T : ι)
    (hMom : ∀ t, Integrable (fun ω => ‖X t ω‖ ^ p) μ)
    (hTerm : MemLp (fun ω => ‖X T ω‖ ^ p) 2 μ) :
    (∫⁻ ω, (⨆ t : Set.Iic T, ENNReal.ofReal (‖X t ω‖ ^ p)) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ENNReal.ofReal (‖X T ω‖ ^ (2 * p)) ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ p) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) p
  have hsub := hmar.submartingale_convex_comp hconv (continuous_norm.pow p) hMom
  have h := submartingale hsub (fun _ _ => pow_nonneg (norm_nonneg _) p)
    (fun ω => (hc ω).continuous_comp (continuous_norm.pow p)) T hTerm
  simpa only [← pow_mul, Nat.mul_comm p 2] using h

end SHEStochastic.DoobL2
