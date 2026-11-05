module

public import SHE.RecursiveReferenceLimit
public import SHE.JointRecursiveHessian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointRecursiveReferenceLimit
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets JointWordAnalytic Filter Topology
open scoped NNReal
local instance jointRecursiveReferenceLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance jointRecursiveReferenceLimit_sigma : MeasurableSpace CircleL2 := borel _
local instance jointRecursiveReferenceLimit_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (δ : ℝ) (hδ : 0<δ) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

theorem reference_eq_average (ε : ℝ≥0) (k : ℕ) (p : History P k) (ω : Ω) :
    reference (level L δ hδ ε k) Λ U V XU XV p ω=
      GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
        ((level L δ hδ ε k).nodeCovariance (p,(R.base,0))).val)
        ((level L δ hδ ε k).test p)
        (state (level L δ hδ ε k) Λ U V XU XV p ω R.base) := by
  unfold reference
  trans gaussianSemigroup R.reference ((level L δ hδ ε k).observations.observations p)
    R.base ((level L δ hδ ε k).terminal p) ((level L δ hδ ε k).test p)
    (state (level L δ hδ ε k) Λ U V XU XV p ω R.base)
  · exact congrFun (PhysicalIto.backward_eq_semigroup ((level L δ hδ ε k).window p)
      ((level L δ hδ ε k).test p) ⟨le_rfl,(level L δ hδ ε k).terminal_base p⟩) _
  change _=GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
    (covariance R.reference ((level L δ hδ ε k).observations.observations p)
      ((level L δ hδ ε k).nodeTime (p,(R.base,0))) ((level L δ hδ ε k).terminal p))) _ _
  rw [RecursiveReferenceLimit.nodeTime_base]
  rfl

/-- Continuity of the literal joint reference, with original-stop
damping in its current mean and the actual epsilon-dependent test. -/
theorem continuous_reference (k : ℕ) (p : History P k) (ω : Ω) :
    Continuous (fun ε : ℝ≥0 => reference (level L δ hδ ε k) Λ U V XU XV p ω) := by
  classical
  cases k with
  | zero =>
    change Continuous (fun _ : ℝ≥0 => reference L Λ U V XU XV p ω)
    exact continuous_const
  | succ k =>
    change History P k×(ℝ×HeatCircle) at p
    by_cases hg : (level L δ hδ 0 k).Good δ p
    · have ht : R.base<(level L δ hδ 0 (k+1)).terminal p := by
        change R.base<(level L δ hδ 0 k).nodeTime p
        rw [(level L δ hδ 0 k).nodeTime_eq hδ hg]
        exact hg.1
      have hm := JointRecursiveHessian.continuous_state L δ hδ Λ U V XU XV (k+1) p ω ht
      have hFs := CutoffWordLevel.uniform_reindex (test_uniform L δ hδ (k+1))
        (fun ε : ℝ≥0 => (ε,p))
      obtain ⟨C,_,hC⟩ := hFs.norm_bound
      have hh := GaussianParameterContinuity.continuous_average
        (fun ε : ℝ≥0 => (level L δ hδ ε (k+1)).test p)
        (RecursiveHeatTestContinuity.continuous_test L δ hδ (k+1) p) hC
        (fun ε => (level L δ hδ ε (k+1)).nodeCovariance (p,(R.base,0)))
        (nodeCovariance_continuous L δ hδ (k+1) (p,(R.base,0)))
      have hc := hh.comp (continuous_id.prodMk hm)
      convert hc using 1
      funext ε
      exact reference_eq_average L δ hδ Λ U V XU XV ε (k+1) p ω
    · have he : (fun ε : ℝ≥0 => reference (level L δ hδ ε (k+1)) Λ U V XU XV p ω)=fun _ => 0 := by
        funext ε
        have hz : (level L δ hδ ε (k+1)).test p=0 := by
          change (level L δ hδ ε k).childTest δ p=0
          rw [CutoffWordLevel.Level.childTest_eq _ hδ p]
          exact if_neg (fun hh => hg ((good_iff L δ hδ ε 0 k p).mp hh))
        unfold reference
        rw [hz]
        simp only [GaussianItoTest.backward,GaussianConvolution.gaussianAverage,Pi.zero_apply,integral_zero]
      rw [he]
      exact continuous_const

/-- Complete history/sample L1 convergence, with delta and finite
smooth depth fixed. This is not a uniform all-orders assertion. -/
theorem integrated_reference_difference_tendsto_zero
    (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
    (ν : Measure P) [IsFiniteMeasure ν] (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ p : History P k×Ω,
      |reference (level L δ hδ ε.toNNReal k) Λ U V XU XV p.1 p.2-
        reference (level L δ hδ 0 k) Λ U V XU XV p.1 p.2| ∂(historyMeasure R ν k).prod τ)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := (test_uniform L δ hδ k).norm_bound
  have hb (ε : ℝ≥0) (p : History P k) (ω : Ω) :
      ‖reference (level L δ hδ ε k) Λ U V XU XV p ω‖≤C := by
    rw [reference_eq_average]
    exact GaussianSmooth.average_norm_bound _ (hCb (ε,p)) _
  have hm (ε : ℝ) : Measurable (fun p : History P k×Ω =>
      |reference (level L δ hδ ε.toNNReal k) Λ U V XU XV p.1 p.2-
        reference (level L δ hδ 0 k) Λ U V XU XV p.1 p.2|) :=
    ((reference_measurable _ Λ hU hV hXU hXV).sub (reference_measurable _ Λ hU hV hXU hXV)).norm
  have ht (p : History P k×Ω) : Tendsto (fun ε : ℝ =>
      |reference (level L δ hδ ε.toNNReal k) Λ U V XU XV p.1 p.2-
        reference (level L δ hδ 0 k) Λ U V XU XV p.1 p.2|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_reference L δ hδ Λ U V XU XV k p.1 p.2).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const (reference (level L δ hδ 0 k) Λ U V XU XV p.1 p.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := (historyMeasure R ν k).prod τ)
    (fun _ => 2*C) (Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hb ε.toNNReal p.1 p.2) (hb 0 p.1 p.2)).trans_eq (by ring)))))
    (integrable_const _) (Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.JointRecursiveReferenceLimit
