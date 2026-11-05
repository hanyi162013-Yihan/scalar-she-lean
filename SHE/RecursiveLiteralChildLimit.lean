module

public import SHE.RecursiveHeatTestContinuity
public import SHE.ObservationTargetContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.RecursiveLiteralChildLimit
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets Filter Topology
open scoped NNReal
local instance recursiveLiteralChildLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance recursiveLiteralChildLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0 < δ)
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

theorem continuous_literalChild (k : ℕ) (p : History P k × (ℝ × HeatCircle)) (ω : Ω) :
    Continuous (fun ε : ℝ≥0 => CutoffWordStep.childLeaf (level L δ hδ ε k) δ U X p ω) := by
  classical
  by_cases hg : (level L δ hδ 0 k).Good δ p
  · have hge (ε : ℝ≥0) : (level L δ hδ ε k).Good δ p := (good_iff L δ hδ ε 0 k p).mpr hg
    let t := (level L δ hδ 0 k).nodeTime p
    have htime (ε : ℝ≥0) : (level L δ hδ ε k).nodeTime p=t := nodeTime_eq L δ hδ ε 0 k p
    have ht (ε : ℝ≥0) (i : Fin (n+k)) : t <
        ((level L δ hδ ε k).observations.observations p.1 i).target := by
      have hh := (level L δ hδ ε k).good_time hδ (hge ε)
      rw [← htime ε]
      rw [(level L δ hδ ε k).nodeTime_eq hδ (hge ε)]
      exact hh.2.trans_le ((level L δ hδ ε k).targets_after p.1 i)
    have hold := ObservationTargetContinuity.continuous_observe
      (fun ε => (level L δ hδ ε k).observations.observations p.1)
      (fun i => ((level L δ hδ 0 k).observations.observations p.1 i).center)
      (target_continuous L δ hδ k p.1) (fun ε i => center_eq L δ hδ ε 0 k p.1 i)
      t ht (fun s => U (ω,s)) (fun q => X (ω,q))
    let V : ℝ≥0 → WordRecursion.State ((n+k)+1) := fun ε => WithLp.toLp 2
      (Fin.cases (X (ω,(t,p.2.2)))
        (observe (fun s => U (ω,s)) (fun q => X (ω,q))
          ((level L δ hδ ε k).observations.observations p.1) t))
    have hV : Continuous V := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin ((n+k)+1) => ℝ)).comp
      apply continuous_pi
      intro i
      refine Fin.cases continuous_const (fun j => ?_) i
      exact (EuclideanSpace.proj j).continuous.comp hold
    have htest := RecursiveHeatTestContinuity.continuous_test L δ hδ (k+1) p
    have hp : Continuous (fun ε : ℝ≥0 => (ε,V ε)) := continuous_id.prodMk hV
    have hc := htest.comp hp
    convert hc using 1
    funext ε
    change (level L δ hδ ε k).childTest δ p _=(level L δ hδ ε k).childTest δ p (V ε)
    congr 1
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if (level L δ hδ ε k).nodeTime p<(level L δ hδ ε k).nodeTime p then _ else _)=_
      rw [if_neg (lt_irrefl _),htime ε]
      rfl
    · change observe (fun s => U (ω,s)) (fun q => X (ω,q))
        ((level L δ hδ ε k).observations.observations p.1) ((level L δ hδ ε k).nodeTime p) j=_
      rw [htime ε]
      rfl
  · have he : (fun ε : ℝ≥0 => CutoffWordStep.childLeaf (level L δ hδ ε k) δ U X p ω)=fun _ => 0 := by
      funext ε
      rw [CutoffWordStep.childLeaf_eq _ δ hδ U X]
      exact if_neg (fun hh => hg ((good_iff L δ hδ ε 0 k p).mp hh))
    rw [he]
    exact continuous_const

/-- The literal zero-age children of the moving recursive tests converge
in full finite history/sample L¹. The ε-dependent tests, covariances,
rows and older observation means all converge by the preceding proofs. -/
theorem integrated_literalChild_difference_tendsto_zero
    (hU : Measurable U) (hX : Measurable X) (μ : Measure P) [IsFiniteMeasure μ]
    (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P (k+1) × Ω,
      |CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ U X q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ 0 k) δ U X q.1 q.2|
      ∂(historyMeasure R μ (k+1)).prod τ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hC,hCb⟩ := (test_uniform L δ hδ (k+1)).norm_bound
  have hb (ε : ℝ≥0) (p : History P k × (ℝ × HeatCircle)) (ω : Ω) :
      ‖CutoffWordStep.childLeaf (level L δ hδ ε k) δ U X p ω‖ ≤ C :=
    hCb (ε,p) _
  have hm (ε : ℝ) : Measurable (fun q : History P (k+1) × Ω =>
      |CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ U X q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ 0 k) δ U X q.1 q.2|) :=
    ((CutoffWordStep.childLeaf_measurable _ δ hδ U X hU hX).sub
      (CutoffWordStep.childLeaf_measurable _ δ hδ U X hU hX)).norm
  have ht (q : History P (k+1) × Ω) :
      Tendsto (fun ε : ℝ => |CutoffWordStep.childLeaf (level L δ hδ ε.toNNReal k) δ U X q.1 q.2-
        CutoffWordStep.childLeaf (level L δ hδ 0 k) δ U X q.1 q.2|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_literalChild L δ hδ U X k q.1 q.2).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const
      (CutoffWordStep.childLeaf (level L δ hδ 0 k) δ U X q.1 q.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence
    (μ := (historyMeasure R μ (k+1)).prod τ) (fun _ => 2*C)
    (Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hb ε.toNNReal q.1 q.2) (hb 0 q.1 q.2)).trans_eq (by ring)))))
    (integrable_const _) (Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.RecursiveLiteralChildLimit
