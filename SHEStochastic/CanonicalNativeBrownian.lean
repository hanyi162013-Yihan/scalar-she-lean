module

public import SHEStochastic.WeakLimitCanonicalBrownian
public import SHE.BrownianShiftedFiniteLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.CanonicalNativeBrownian
open MeasureTheory ProbabilityTheory SHE
open CanonicalStateDriverFiltration WeakLimitCanonicalBrownian
open scoped NNReal

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι)
  (U : ℝ≥0 → Ω → E) (hc : ∀ sample, Continuous (fun t ↦ U t sample))
  (hU : ∀ t, Measurable[F t] (U t))

/-- Centering at time zero makes every canonical driver start at zero
pointwise and leaves all increments and native integrals unchanged. -/
def bundle := CanonicalFutureStateDriver.bundle U hc P.W P.continuous 0 H

include hU in
theorem measurable_bundle : Measurable (bundle F μ H P U hc) :=
  CanonicalFutureStateDriver.measurable_bundle F U hc P.W P.continuous hU P.adapted 0 H

theorem clock_time (q : ℝ≥0) (hq : q ≤ H) : (clock H q).val.toNNReal = q := by
  change (min (q : ℝ) (H : ℝ)).toNNReal = q
  rw [min_eq_left (by exact_mod_cast hq), Real.toNNReal_coe]

theorem observation_comp {n : ℕ} (a : Fin n → ι) (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ H) :
    (observation H a t) ∘ bundle F μ H P U hc = fun sample ↦
      (WithLp.toLp 2 (fun i ↦ P.W (a i) (0 + t i) sample - P.W (a i) 0 sample) : WordRecursion.State n) := by
  funext sample
  apply PiLp.ext
  intro i
  change P.W (a i) (0 + (clock H (t i)).val.toNNReal) sample - P.W (a i) 0 sample = _
  rw [clock_time H (t i) (ht i)]

theorem increment_comp {n : ℕ} (a : Fin n → ι) (s t : ℝ≥0) (hs : s ≤ H) (ht : t ≤ H) :
    (increment H a s t) ∘ bundle F μ H P U hc = fun sample ↦
      (WithLp.toLp 2 (fun i ↦ P.W (a i) t sample - P.W (a i) s sample) : WordRecursion.State n) := by
  funext sample
  apply PiLp.ext
  intro i
  change (P.W (a i) (0 + (clock H t).val.toNNReal) sample - P.W (a i) 0 sample) -
    (P.W (a i) (0 + (clock H s).val.toNNReal) sample - P.W (a i) 0 sample) = _
  rw [clock_time H t ht, clock_time H s hs, zero_add, zero_add]
  abel

include hU in
theorem past_adapted (s : ℝ≥0) (hs : s ≤ H) :
    Measurable[F s] ((history (E := E) (ι := ι) H s) ∘ bundle F μ H P U hc) := by
  have hh := CanonicalFutureStateDriver.adapted_past F U hc P.W P.continuous hU P.adapted
    0 H (clock H s)
  change Measurable[F (0 + (clock H s).val.toNNReal)]
    ((history (E := E) (ι := ι) H s) ∘ bundle F μ H P U hc) at hh
  rw [clock_time H s hs, zero_add] at hh
  exact hh

include hU in
/-- Canonical paths are frozen at the horizon; their full past at any
later observation is measurable at the corresponding capped time. -/
theorem past_adapted_capped (s : ℝ≥0) :
    Measurable[F (min s H)] ((history (E := E) (ι := ι) H s) ∘ bundle F μ H P U hc) := by
  have hh := CanonicalFutureStateDriver.adapted_past F U hc P.W P.continuous hU P.adapted
    0 H (clock H s)
  change Measurable[F (0+(clock H s).val.toNNReal)]
    ((history (E := E) (ι := ι) H s) ∘ bundle F μ H P U hc) at hh
  have ht : (clock H s).val.toNNReal = min s H := by
    change (min (s : ℝ) (H : ℝ)).toNNReal = min s H
    rw [← NNReal.coe_min, Real.toNNReal_coe]
  rwa [ht, zero_add] at hh

include hU in
/-- Passing an actual adapted state and native Brownian driver to their
joint canonical path law retains Gaussian finite laws and independence
from the entire canonical STATE and DRIVER history. -/
theorem law (n : ℕ) (a : Fin n → ι) :
    FiniteBrownianLawOn (filtration (E := E) (ι := ι) H)
      (μ.map (bundle F μ H P U hc)) H (fun i ↦ coordinate H (a i))
      (fun i j ↦ if a i = a j then 1 else 0) := by
  have hm := measurable_bundle F μ H P U hc hU
  constructor
  · intro t ht
    have hr := BrownianShiftedFiniteLaw.law F μ H P.W P.law 0 H (by simp) a t ht
    refine ⟨(continuous_observation H a t).measurable.aemeasurable, ?_⟩
    change (μ.map (bundle F μ H P U hc)).map (observation H a t) =
      multivariateGaussian 0 (BrownianFiniteCovariance.matrix a t)
    rw [Measure.map_map (continuous_observation H a t).measurable hm,
      observation_comp F μ H P U hc a t ht]
    exact hr.map_eq
  · intro s t hst ht
    have hs := hst.trans ht
    have hpast := past_adapted F μ H P U hc hU s hs
    have hi : IndepFun ((history (E := E) (ι := ι) H s) ∘ bundle F μ H P U hc)
        ((increment H a s t) ∘ bundle F μ H P U hc) μ := by
      rw [increment_comp F μ H P U hc a s t hs ht]
      exact indep_of_indep_of_le_left ((P.law n a).2 s t hst ht).symm hpast.comap_le
    have hh : IndepFun (history (E := E) (ι := ι) H s) (increment H a s t)
        (μ.map (bundle F μ H P U hc)) := by
      apply (indepFun_iff_map_prod_eq_prod_map_map
        (continuous_history H s).measurable.aemeasurable
        (continuous_increment H a s t).measurable.aemeasurable).mpr
      rw [Measure.map_map ((continuous_history H s).prodMk
        (continuous_increment H a s t)).measurable hm,
        Measure.map_map (continuous_history H s).measurable hm,
        Measure.map_map (continuous_increment H a s t).measurable hm]
      exact hi.map_prod_eq_prod_map_map (hpast.mono (F.le s) le_rfl).aemeasurable
        ((continuous_increment H a s t).measurable.comp hm).aemeasurable
    exact hh.symm

end SHEStochastic.CanonicalNativeBrownian
