module

public import SHE.RecursiveHeatTestContinuity
public import SHE.ObservationTargetContinuity
public import SHE.CutoffReferenceTree

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.RecursiveReferenceLimit
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets CutoffReferenceTree Filter Topology
open scoped NNReal
local instance recursiveReferenceLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveReferenceLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P : Type*} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)

theorem nodeTime_base (ε : ℝ≥0) (k : ℕ) (p : History P k) (x : HeatCircle) :
    (level L δ hδ ε k).nodeTime (p,(R.base,x))=R.base := by
  exact ClippedCovariance.clip_eq ⟨le_rfl,(level L δ hδ ε k).terminal_base p⟩

theorem reference_eq_average (ε : ℝ≥0) (k : ℕ) (p : History P k) (u : CircleL2) :
    deterministicReference (level L δ hδ ε k) u p=
      GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
        ((level L δ hδ ε k).nodeCovariance (p,(R.base,0))).val)
        ((level L δ hδ ε k).test p)
        (CanonicalConditional.initialMean ((level L δ hδ ε k).observations.observations p) R.base u) := by
  unfold deterministicReference
  trans gaussianSemigroup R.reference ((level L δ hδ ε k).observations.observations p)
    R.base ((level L δ hδ ε k).terminal p) ((level L δ hδ ε k).test p)
    (CanonicalConditional.initialMean ((level L δ hδ ε k).observations.observations p) R.base u)
  · exact congrFun (PhysicalIto.backward_eq_semigroup ((level L δ hδ ε k).window p)
      ((level L δ hδ ε k).test p) ⟨le_rfl,(level L δ hδ ε k).terminal_base p⟩) _
  change _=GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
    (covariance R.reference ((level L δ hδ ε k).observations.observations p)
      ((level L δ hδ ε k).nodeTime (p,(R.base,0))) ((level L δ hδ ε k).terminal p))) _ _
  rw [nodeTime_base]
  rfl

/-- Genuine continuity of each recursively ε-dependent deterministic
reference word, including ε=0. Inactive cutoff histories have the zero
test, so no point evaluation of an arbitrary L² state is introduced. -/
theorem continuous_reference (k : ℕ) (p : History P k) (u : CircleL2) :
    Continuous (fun ε : ℝ≥0 => deterministicReference (level L δ hδ ε k) u p) := by
  classical
  cases k with
  | zero =>
    change Continuous (fun _ : ℝ≥0 => deterministicReference L u p)
    exact continuous_const
  | succ k =>
    change History P k × (ℝ × HeatCircle) at p
    by_cases hg : (level L δ hδ 0 k).Good δ p
    · have hge (ε : ℝ≥0) : (level L δ hδ ε k).Good δ p := (good_iff L δ hδ ε 0 k p).mpr hg
      have ht (ε : ℝ≥0) (i : Fin (n+(k+1))) : R.base<
          ((level L δ hδ ε (k+1)).observations.observations p i).target := by
        refine Fin.cases ?_ (fun j => ?_) i
        · change R.base<(level L δ hδ ε k).nodeTime p+(ε:ℝ)
          rw [(level L δ hδ ε k).nodeTime_eq hδ (hge ε)]
          linarith [(hge ε).1,ε.2]
        · change R.base<((level L δ hδ ε k).observations.observations p.1 j).target
          exact ((level L δ hδ ε k).good_time hδ (hge ε)).1.trans
            (((level L δ hδ ε k).good_time hδ (hge ε)).2.trans_le
              ((level L δ hδ ε k).targets_after p.1 j))
      have hm := ObservationTargetContinuity.continuous_initialMean
        (fun ε => (level L δ hδ ε (k+1)).observations.observations p)
        (fun i => ((level L δ hδ 0 (k+1)).observations.observations p i).center)
        (target_continuous L δ hδ (k+1) p) (fun ε i => center_eq L δ hδ ε 0 (k+1) p i)
        R.base ht u
      have hFs := CutoffWordLevel.uniform_reindex (test_uniform L δ hδ (k+1))
        (fun ε : ℝ≥0 => (ε,p))
      obtain ⟨C,_,hC⟩ := hFs.norm_bound
      have hF := RecursiveHeatTestContinuity.continuous_test L δ hδ (k+1) p
      have hA := nodeCovariance_continuous L δ hδ (k+1) (p,(R.base,0))
      have hh := GaussianParameterContinuity.continuous_average
        (fun ε : ℝ≥0 => (level L δ hδ ε (k+1)).test p) hF hC
        (fun ε => (level L δ hδ ε (k+1)).nodeCovariance (p,(R.base,0))) hA
      have hc := hh.comp (continuous_id.prodMk hm)
      convert hc using 1
      funext ε
      exact reference_eq_average L δ hδ ε (k+1) p u
    · have he : (fun ε : ℝ≥0 => deterministicReference (level L δ hδ ε (k+1)) u p)=fun _ => 0 := by
        funext ε
        have hz : (level L δ hδ ε (k+1)).test p=0 := by
          change (level L δ hδ ε k).childTest δ p=0
          rw [CutoffWordLevel.Level.childTest_eq _ hδ p]
          exact if_neg (fun hh => hg ((good_iff L δ hδ ε 0 k p).mp hh))
        unfold deterministicReference
        rw [hz]
        simp only [GaussianItoTest.backward,GaussianConvolution.gaussianAverage,Pi.zero_apply,integral_zero]
      rw [he]
      exact continuous_const

theorem integrated_reference_difference_tendsto_zero
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) (u : CircleL2) :
    Tendsto (fun ε : ℝ => ∫ p : History P k,
      |deterministicReference (level L δ hδ ε.toNNReal k) u p-
        deterministicReference (level L δ hδ 0 k) u p| ∂historyMeasure R μ k)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := (test_uniform L δ hδ k).norm_bound
  have hb (ε : ℝ≥0) (p : History P k) : ‖deterministicReference (level L δ hδ ε k) u p‖ ≤ C := by
    rw [reference_eq_average]
    exact GaussianSmooth.average_norm_bound _ (hCb (ε,p)) _
  have hm (ε : ℝ) : Measurable (fun p : History P k =>
      |deterministicReference (level L δ hδ ε.toNNReal k) u p-
        deterministicReference (level L δ hδ 0 k) u p|) :=
    ((deterministicReference_measurable _ u).sub (deterministicReference_measurable _ u)).norm
  have ht (p : History P k) : Tendsto (fun ε : ℝ =>
      |deterministicReference (level L δ hδ ε.toNNReal k) u p-
        deterministicReference (level L δ hδ 0 k) u p|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_reference L δ hδ k p u).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const (deterministicReference (level L δ hδ 0 k) u p)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := historyMeasure R μ k) (fun _ => 2*C)
    (Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hb ε.toNNReal p) (hb 0 p)).trans_eq (by ring)))))
    (integrable_const _) (Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.RecursiveReferenceLimit
