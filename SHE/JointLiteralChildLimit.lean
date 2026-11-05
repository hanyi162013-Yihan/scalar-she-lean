module

public import SHE.RecursiveHeatTestContinuity
public import SHE.JointObservationTargetContinuity
public import SHE.JointCutoffStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointLiteralChildLimit
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
open RecursiveHeatBounds RecursiveHeatTargets Filter Topology
open scoped NNReal
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (δ : ℝ) (hδ : 0<δ) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

/-- Continuity of the actual moving old-joint test, with every original
stop and shifted heat target carried through the recursive history. -/
theorem continuous_literalChild (k : ℕ) (p : History P k×(ℝ×HeatCircle)) (ω : Ω) :
    Continuous (fun ε : ℝ≥0 => JointCutoffStep.childLeaf (level L δ hδ ε k) Λ δ U V XU XV p ω) := by
  classical
  by_cases hg : (level L δ hδ 0 k).Good δ p
  · have hge (ε : ℝ≥0) : (level L δ hδ ε k).Good δ p := (good_iff L δ hδ ε 0 k p).mpr hg
    let t := (level L δ hδ 0 k).nodeTime p
    have htime (ε : ℝ≥0) : (level L δ hδ ε k).nodeTime p=t := nodeTime_eq L δ hδ ε 0 k p
    have ht (ε : ℝ≥0) (i : Fin (n+k)) : t<((level L δ hδ ε k).observations.observations p.1 i).target := by
      have hh := (level L δ hδ ε k).good_time hδ (hge ε)
      rw [← htime ε,(level L δ hδ ε k).nodeTime_eq hδ (hge ε)]
      exact hh.2.trans_le ((level L δ hδ ε k).targets_after p.1 i)
    have hσ (i : Fin (n+k)) : Continuous (fun ε : ℝ≥0 =>
        ((level L δ hδ ε k).observations.observations p.1 i).stop) := by
      convert (continuous_const (y := ((level L δ hδ 0 k).observations.observations p.1 i).stop)) using 1
      funext ε
      exact stop_eq L δ hδ ε 0 k p.1 i
    have hold := JointObservationTargetContinuity.continuous_evaluate Λ
      (fun ε => (level L δ hδ ε k).observations.observations p.1)
      (fun i => ((level L δ hδ 0 k).observations.observations p.1 i).center)
      (target_continuous L δ hδ k p.1) hσ (fun ε i => center_eq L δ hδ ε 0 k p.1 i)
      t ht (fun s => U (ω,s)) (fun s => V (ω,s)) (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx))
    let W : ℝ≥0→WordRecursion.State ((n+k)+1) := fun ε =>
      JointPhysicalInsertion.appendState (XV (ω,(t,p.2.2)))
        (JointWordObserve.evaluate Λ (fun s => U (ω,s)) (fun s => V (ω,s))
          (fun tx => XU (ω,tx)) (fun tx => XV (ω,tx))
          ((level L δ hδ ε k).observations.observations p.1) t)
    have hW : Continuous W := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin ((n+k)+1) => ℝ)).comp
      apply continuous_pi
      intro i
      refine Fin.cases continuous_const (fun j => ?_) i
      exact (EuclideanSpace.proj j).continuous.comp hold
    have hc := (RecursiveHeatTestContinuity.continuous_test L δ hδ (k+1) p).comp (continuous_id.prodMk hW)
    convert hc using 1
    funext ε
    change (level L δ hδ ε k).childTest δ p
      (JointWordObserve.evaluate Λ _ _ _ _ (appendObservation _ ((level L δ hδ ε k).nodeTime p) p.2.2)
        ((level L δ hδ ε k).nodeTime p))=(level L δ hδ ε k).childTest δ p (W ε)
    rw [JointWordObserve.evaluate_append,htime ε]
  · have he : (fun ε : ℝ≥0 => JointCutoffStep.childLeaf (level L δ hδ ε k) Λ δ U V XU XV p ω)=fun _ => 0 := by
      funext ε
      rw [JointCutoffStep.childLeaf_eq _ Λ δ hδ]
      exact ite_eq_right (fun hh => hg ((good_iff L δ hδ ε 0 k p).mp hh))
    rw [he]
    exact continuous_const

/-- Full history/sample L1 convergence for recursively moving literal
joint children at fixed finite depth and positive time cutoff. -/
theorem integrated_literalChild_difference_tendsto_zero
    (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
    (ν : Measure P) [IsFiniteMeasure ν] (τ : Measure Ω) [IsFiniteMeasure τ] (k : ℕ) :
    Tendsto (fun ε : ℝ => ∫ q : History P (k+1)×Ω,
      |JointCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) Λ δ U V XU XV q.1 q.2-
        JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ U V XU XV q.1 q.2|
      ∂(historyMeasure R ν (k+1)).prod τ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,hCn,hC⟩ := (test_uniform L δ hδ (k+1)).norm_bound
  have hb (ε : ℝ≥0) (p : History P k×(ℝ×HeatCircle)) (ω : Ω) :
      ‖JointCutoffStep.childLeaf (level L δ hδ ε k) Λ δ U V XU XV p ω‖≤C := hC (ε,p) _
  have hm (ε : ℝ) : Measurable (fun q : History P (k+1)×Ω =>
      |JointCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) Λ δ U V XU XV q.1 q.2-
        JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ U V XU XV q.1 q.2|) :=
    ((JointCutoffStep.childLeaf_measurable _ Λ δ hU hV hXU hXV hδ).sub
      (JointCutoffStep.childLeaf_measurable _ Λ δ hU hV hXU hXV hδ)).norm
  have ht (q : History P (k+1)×Ω) : Tendsto (fun ε : ℝ =>
      |JointCutoffStep.childLeaf (level L δ hδ ε.toNNReal k) Λ δ U V XU XV q.1 q.2-
        JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ U V XU XV q.1 q.2|)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := (continuous_literalChild L δ hδ Λ U V XU XV k q.1 q.2).comp continuous_real_toNNReal
    have hh := ((hc.tendsto (0:ℝ)).sub_const (JointCutoffStep.childLeaf (level L δ hδ 0 k) Λ δ U V XU XV q.1 q.2)).norm
    simpa only [Function.comp_def,Real.toNNReal_zero,sub_self,norm_zero,Real.norm_eq_abs] using
      hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := (historyMeasure R ν (k+1)).prod τ)
    (fun _ => 2*C) (Filter.Eventually.of_forall (fun ε => (hm ε).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs,abs_abs]
      exact (norm_sub_le _ _).trans ((add_le_add (hb ε.toNNReal q.1 q.2) (hb 0 q.1 q.2)).trans_eq (by ring)))))
    (integrable_const _) (Filter.Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.JointLiteralChildLimit
