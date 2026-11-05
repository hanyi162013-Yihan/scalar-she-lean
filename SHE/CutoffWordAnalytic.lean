module

public import SHE.CutoffWordLevel
public import SHE.IntegratedPhysicalStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Deterministic analytic conditions for actual cutoff-history words.
The observation lists vary with every history. All profiles and bracket
coefficients in this module are TOTAL variances. -/
noncomputable section
namespace SHE.CutoffWordAnalytic
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion CovarianceEndpoint GaussianContinuity GaussianItoTest GaussianConvolution
open CutoffWordLevel VariableObservations MeasurableWords UniformSmooth
open IntegratedPhysicalStep PhysicalIto
open Classical

abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)

theorem path_measurable : Measurable (fun p : P × ℝ => (L.window p.1).path p.2) := by
  let Z : Family (P × ℝ) n := reindexFamily L.observations Prod.fst measurable_fst
  have ht : Measurable (fun p : P × ℝ => ClippedCovariance.clip R.base (L.terminal p.1) p.2) :=
    measurable_const.max ((L.terminal_measurable.comp measurable_fst).min measurable_snd)
  exact Z.positive_covariance_measurable (R.reference_measurable.comp measurable_snd)
    ht (L.terminal_measurable.comp measurable_fst)
    (fun p => (ClippedCovariance.clip_mem (L.terminal_base p.1) p.2).2)
    (fun p => ((L.window p.1).path p.2).property)

theorem backward_measurable :
    Measurable (fun p : (P × ℝ) × State n => backward (L.window p.1.1) (L.test p.1.1) p.1.2 p.2) := by
  exact gaussian_average_measurable (path_measurable L)
    (L.test_measurable.comp (measurable_fst.fst.prodMk measurable_snd))
    (fun p => (L.test_uniform.smooth p.1).continuous)

theorem backward_uniform : UniformBoundedSmooth
    (fun p : P × ℝ => backward (L.window p.1) (L.test p.1) p.2) :=
  (uniform_reindex L.test_uniform Prod.fst).average
    (fun p => multivariateGaussian (0 : State n) ((L.window p.1).path p.2).val) (fun _ => inferInstance)

def physicalLevel (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)
    (N : P → (ℝ → State n → ℝ) → Ω → ℝ) : LevelData P Ω n where
  window := L.window
  totalVariance := R.totalVariance
  state := fun _ ω t => U (ω,t)
  field := fun _ ω q => X (ω,q)
  test := L.test
  stochasticTerm := N

theorem physical_observe_measurable {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X) :
    Measurable (fun p : (P × Ω) × ℝ => observe (fun t => U (p.1.2,t))
      (fun q => X (p.1.2,q)) (L.observations.observations p.1.1) p.2) := by
  let Z : Family (P × Ω) n := reindexFamily L.observations Prod.fst measurable_fst
  exact Z.observe_measurable (hU.comp (measurable_fst.snd.prodMk measurable_snd))
    (hX.comp (measurable_fst.snd.prodMk measurable_snd))

theorem physical_leaf_measurable {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    (N : P → (ℝ → State n → ℝ) → Ω → ℝ) :
    Measurable (fun p : P × Ω => (physicalLevel L U X N).leaf p.1 p.2) := by
  have hY := (physical_observe_measurable L hU hX).comp
    (measurable_id.prodMk (L.terminal_measurable.comp measurable_fst))
  exact L.test_measurable.comp (measurable_fst.prodMk hY)

set_option backward.isDefEq.respectTransparency true in
theorem physical_reference_measurable {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    (N : P → (ℝ → State n → ℝ) → Ω → ℝ) :
    Measurable (fun p : P × Ω => (physicalLevel L U X N).reference p.1 p.2) := by
  change Measurable (fun p : P × Ω => backward (L.window p.1) (L.test p.1) R.base
    (observe (fun t => U (p.2,t)) (fun q => X (p.2,q)) (L.observations.observations p.1) R.base))
  have hY : Measurable (fun p : P × Ω => observe (fun t => U (p.2,t))
      (fun q => X (p.2,q)) (L.observations.observations p.1) R.base) :=
    (physical_observe_measurable L hU hX).comp
    (measurable_id.prodMk (measurable_const (a := R.base)))
  have hmap : Measurable (fun p : P × Ω => ((p.1, R.base),
      observe (fun t => U (p.2,t)) (fun q => X (p.2,q)) (L.observations.observations p.1) R.base)) :=
    ((measurable_fst.prodMk (measurable_const (a := R.base))).prodMk hY)
  have hout := backward_measurable L
  have hcomp := hout.comp hmap
  simpa only [Function.comp_def] using hcomp

set_option backward.isDefEq.respectTransparency true in
theorem physical_insertion_measurable {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X) :
    Measurable (fun p : ((P × Ω) × ℝ) × HeatCircle => insertedWord (L.window p.1.1.1)
      R.totalVariance (fun t => U (p.1.1.2,t)) (fun q => X (p.1.1.2,q))
      (L.test p.1.1.1) p.1.2 p.2) := by
  have hY : Measurable (fun p : ((P × Ω) × ℝ) × HeatCircle =>
      observe (fun t => U (p.1.1.2,t)) (fun q => X (p.1.1.2,q))
        (L.observations.observations p.1.1.1) p.1.2) :=
    (physical_observe_measurable L hU hX).comp measurable_fst
  have hG : Measurable (fun p : (P × ℝ) × State n =>
      GaussianTaylor.hessian (backward (L.window p.1.1) (L.test p.1.1) p.1.2) p.2) :=
    MeasurableDerivatives.hessian_measurable (backward_measurable L)
      (fun p => ((backward_uniform L).smooth p).of_le (by simp))
  have hH := hG.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk hY)
  have hrowMap : Measurable (fun p : ((P × Ω) × ℝ) × HeatCircle =>
      (p.1.1.1,(p.1.2,p.2))) :=
    measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hrow := L.observations.heatRow_measurable.comp hrowMap
  have he₁ : Continuous (fun p : (State n →L[ℝ] State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have he₂ : Continuous (fun p : (State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hdir := he₂.measurable.comp ((he₁.measurable.comp (hH.prodMk hrow)).prodMk hrow)
  have hcoef : Measurable (fun p : ((P × Ω) × ℝ) × HeatCircle =>
      R.totalVariance (X (p.1.1.2,(p.1.2,p.2))) - R.reference (p.1.2,p.2)) :=
    (R.totalVariance_smooth.smooth.continuous.measurable.comp
    (hX.comp (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd)))).sub
    (R.reference_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have hresult := (hcoef.const_mul (1 / 2 : ℝ)).mul hdir
  have heq : (fun p : ((P × Ω) × ℝ) × HeatCircle => insertedWord (L.window p.1.1.1)
      R.totalVariance (fun t => U (p.1.1.2,t)) (fun q => X (p.1.1.2,q))
      (L.test p.1.1.1) p.1.2 p.2) = (fun p => (1 / 2 : ℝ) *
        (R.totalVariance (X (p.1.1.2,(p.1.2,p.2))) - R.reference (p.1.2,p.2)) *
        directionalSecond (backward (L.window p.1.1.1) (L.test p.1.1.1) p.1.2)
          (observe (fun t => U (p.1.1.2,t)) (fun q => X (p.1.1.2,q))
            (L.observations.observations p.1.1.1) p.1.2)
          (heatRow (L.observations.observations p.1.1.1) p.1.2 p.2)) := by
    funext p
    exact insertion_observe R.totalVariance R.reference (fun t => U (p.1.1.2,t))
      (fun q => X (p.1.1.2,q)) (L.observations.observations p.1.1.1) p.1.2 p.2 _
  rw [heq]
  exact hresult

theorem physical_remainder_measurable {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    (N : P → (ℝ → State n → ℝ) → Ω → ℝ) :
    Measurable (fun p : P × Ω => (physicalLevel L U X N).remainder p.1 p.2) := by
  have hi := (physical_insertion_measurable L hU hX).stronglyMeasurable.integral_prod_right'
    (ν := AddCircle.haarAddCircle)
  have hs : MeasurableSet {p : (P × Ω) × ℝ | R.base < p.2 ∧ p.2 ≤ L.terminal p.1.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (L.terminal_measurable.comp measurable_fst.fst))
  have hm : Measurable (fun p : (P × Ω) × ℝ => if R.base < p.2 ∧ p.2 ≤ L.terminal p.1.1 then
      ∫ x, insertedWord (L.window p.1.1) R.totalVariance (fun t => U (p.1.2,t))
        (fun q => X (p.1.2,q)) (L.test p.1.1) p.2 x ∂AddCircle.haarAddCircle else 0) :=
    hi.measurable.ite hs measurable_const
  have ht := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert ht.measurable using 1
  funext p
  change (∫ t in R.base..L.terminal p.1, _) = _
  rw [intervalIntegral.integral_of_le (L.terminal_base p.1), ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator, mem_Ioc]
  rfl

theorem physical_analyticConditions {U : Ω × ℝ → CircleL2} (hU : Measurable U)
    {X : Ω × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    (N : P → (ℝ → State n → ℝ) → Ω → ℝ) :
    AnalyticConditions (physicalLevel L U X N) := by
  obtain ⟨A,hAn,hA⟩ := (UniformBoundedSmooth.fixed (P := Unit) R.totalVariance_smooth).norm_bound
  refine ⟨R.totalVariance_smooth.smooth.continuous.measurable,
    ⟨A,R.upper,R.horizon,hAn,R.upper_nonneg,R.base_nonneg.trans R.ordered,
      ?_,fun _ => le_rfl,fun _ => R.base_nonneg,L.terminal_horizon⟩,
    L.test_uniform, physical_leaf_measurable L hU hX N,
    physical_reference_measurable L hU hX N,physical_remainder_measurable L hU hX N⟩
  intro z
  change |R.totalVariance z| ≤ A
  simpa only [Real.norm_eq_abs] using hA () z

end SHE.CutoffWordAnalytic
