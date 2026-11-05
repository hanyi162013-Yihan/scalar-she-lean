module

public import SHE.RecursiveRemainderLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.RecursiveRemainderConvergence
open Set MeasureTheory AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets CutoffWordAnalytic Filter Topology
open PhysicalIto PhysicalRemainderBound PhysicalRemainderMass RecursiveRemainderLimit
open scoped NNReal
local instance recursiveRemainderConvergence_period : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance recursiveRemainderConvergence_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveRemainderConvergence_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

def remainder (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  wordRemainder ((level L δ hδ ε k).window p) R.totalVariance
    (fun t => U (ω,t)) (fun q => X (ω,q)) ((level L δ hδ ε k).test p)

theorem uniform_spatial_bound (k : ℕ) : ∃ K : ℝ,0 ≤ K ∧ ∀ ε : ℝ≥0,∀ p ω t,
    t ∈ Ioo R.base ((level L δ hδ 0 k).terminal p) →
    ‖spatial L δ hδ U X ε k p ω t‖ ≤
      K*(1+heatConstant*((level L δ hδ 0 k).terminal p-t)^(-(1/2:ℝ))) := by
  obtain ⟨A,hA⟩ := R.totalVariance_smooth.norm_bound
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩ := (test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let K : ℝ := (1/2:ℝ)*(A+R.upper)*B*((n+k:ℕ):ℝ)
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _),fun ε p ω t ht => ?_⟩
  have hte : t ∈ Ioo ((level L δ hδ ε k).window p).left ((level L δ hδ ε k).window p).right := by
    change t ∈ Ioo R.base ((level L δ hδ ε k).terminal p)
    rw [terminal_eq L δ hδ ε 0 k p]
    exact ht
  have hHb : ∀ z,‖GaussianTaylor.hessian (GaussianItoTest.backward
      ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) z‖ ≤ B :=
    fun z => BackwardRegularity.gaussian_state_hessian_bound _
      (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p)) z
  have hh := inserted_spatial_norm_bound ((level L δ hδ ε k).window p) hAn
    (fun z => by simpa only [Real.norm_eq_abs] using hA z) hBn (fun t => U (ω,t)) (fun q => X (ω,q))
    hte (GaussianItoTest.backward ((level L δ hδ ε k).window p) ((level L δ hδ ε k).test p) t) hHb
  change ‖spatial L δ hδ U X ε k p ω t‖ ≤ K*(1+heatConstant*((level L δ hδ ε k).terminal p-t)^(-(1/2:ℝ))) at hh
  rw [terminal_eq L δ hδ ε 0 k p] at hh
  exact hh

theorem uniform_remainder_bound (k : ℕ) : ∃ K : ℝ,0 ≤ K ∧ ∀ ε : ℝ≥0,∀ p ω,
    ‖remainder L δ hδ U X ε k p ω‖ ≤ K := by
  obtain ⟨A,hA⟩ := R.totalVariance_smooth.norm_bound
  have hAn : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  obtain ⟨C,_,hC⟩ := (test_uniform L δ hδ k).norm_bound
  obtain ⟨D,_,hD⟩ := (test_uniform L δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (test_uniform L δ hδ k).fderiv.fderiv.norm_bound
  let K : ℝ := ((1/2:ℝ)*(A+R.upper)*B*((n+k:ℕ):ℝ))*heatMass R.horizon
  have hhorizon : 0 ≤ R.horizon := R.base_nonneg.trans R.ordered
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _))
    (heatMass_nonneg hhorizon),fun ε p ω => ?_⟩
  exact remainder_horizon_bound ((level L δ hδ ε k).window p) hAn
    (fun z => by simpa only [Real.norm_eq_abs] using hA z) hBn (le_rfl : R.upper ≤ R.upper)
    R.base_nonneg ((level L δ hδ ε k).terminal_horizon p) (fun t => U (ω,t)) (fun q => X (ω,q))
    (((level L δ hδ ε k).test_uniform.smooth p).of_le (by simp)) (hC (ε,p)) (hD (ε,p)) (hB (ε,p))

/-- The actual moving physical remainder is continuous in ε through zero.
Spatial domination is local in t; the subsequent time integration uses
the sharp integrable heat-square endpoint bound rather than its square. -/
theorem continuous_remainder (hU : Measurable U) (hX : Measurable X)
    (k : ℕ) (p : History P k) (ω : Ω) :
    Continuous (fun ε : ℝ≥0 => remainder L δ hδ U X ε k p ω) := by
  obtain ⟨K,hK,hKb⟩ := uniform_spatial_bound L δ hδ U X k
  let s := (level L δ hδ 0 k).terminal p
  have hs : R.base ≤ s := (level L δ hδ 0 k).terminal_base p
  have he : (fun ε : ℝ≥0 => remainder L δ hδ U X ε k p ω)=
      fun ε => ∫ t,spatial L δ hδ U X ε k p ω t ∂volume.restrict (Ioc R.base s) := by
    funext ε
    change (∫ t in R.base..(level L δ hδ ε k).terminal p,spatial L δ hδ U X ε k p ω t)=_
    rw [terminal_eq L δ hδ ε 0 k p,intervalIntegral.integral_of_le hs]
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => K*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro ε
    have hp : Measurable (fun t : ℝ => ((p,ω),t)) := measurable_const.prodMk measurable_id
    have hc := (spatial_measurable L δ hδ U X hU hX ε k).comp hp
    exact hc.aestronglyMeasurable
  · intro ε
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact hKb ε p ω t ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := R.base) (s := s) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact continuous_spatial L δ hδ U X hU hX k p ω ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩

/-- Full finite-history/sample L¹ convergence of the recursively moving
actual remainders, with δ and depth fixed. This is an analytic theorem
for arbitrary jointly measurable physical state and field. -/
theorem integrated_remainder_difference_tendsto_zero (hU : Measurable U) (hX : Measurable X)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P k × Ω,
      |remainder L δ hδ U X ε.toNNReal k q.1 q.2-remainder L δ hδ U X 0 k q.1 q.2|
      ∂(historyMeasure R μ k).prod τ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨K,hK,hKb⟩ := uniform_remainder_bound L δ hδ U X k
  have hm (ε : ℝ) : Measurable (fun q : History P k × Ω =>
      |remainder L δ hδ U X ε.toNNReal k q.1 q.2-remainder L δ hδ U X 0 k q.1 q.2|) :=
    ((physical_remainder_measurable (level L δ hδ ε.toNNReal k) hU hX (fun _ _ _ => 0)).sub
      (physical_remainder_measurable (level L δ hδ 0 k) hU hX (fun _ _ _ => 0))).norm
  have ht (q : History P k × Ω) : Tendsto (fun ε : ℝ =>
      |remainder L δ hδ U X ε.toNNReal k q.1 q.2-remainder L δ hδ U X 0 k q.1 q.2|)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_remainder L δ hδ U X hU hX k q.1 q.2).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const (remainder L δ hδ U X 0 k q.1 q.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := (historyMeasure R μ k).prod τ)
    (fun _ => 2*K) (Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hKb ε.toNNReal q.1 q.2) (hKb 0 q.1 q.2)).trans_eq (by ring)))))
    (integrable_const _) (Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.RecursiveRemainderConvergence
