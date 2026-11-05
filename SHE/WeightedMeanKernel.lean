module

public import SHE.StopWeightedRows
public import SHE.SeparatedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders StopWeightedRows
local instance weightedMeanKernel_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The literal signed-difference direction of the joint diffusion.
Both its Gaussian law and its stop-dependent weights stay at q when
the physical heat row is moved to r. -/
def weightedPoint (k : ℕ) (Λ q r : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) : ℝ :=
  if q < (carrier L k).terminal p ∧ r < (carrier L k).terminal p then
    fderiv ℝ (gaussianAverage (covariance R.reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (m p)
      (weightedHeatRow Λ ((carrier L k).observations.observations p) q r y)
  else 0

def weightedSpatial (k : ℕ) (Λ q r : ℝ)
    (m : X → History P k → WordRecursion.State (n+k)) (t : Fin k → ℝ)
    (x : X) (y : HeatCircle) (p : P) : ℂ :=
  ((∫ z : Fin k → HeatCircle,weightedPoint L k Λ q r (m x) (separated k (p,t,z)) y
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ)

theorem weightedPoint_of_active (k : ℕ) (Λ q r : ℝ)
    (m : History P k → WordRecursion.State (n+k)) (p : History P k) (y : HeatCircle)
    (hq : q < (carrier L k).terminal p) (hr : r < (carrier L k).terminal p) :
    weightedPoint L k Λ q r m p y=
      fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) (m p)
        (weightedHeatRow Λ ((carrier L k).observations.observations p) q r y) := by
  exact ite_eq_left ⟨hq,hr⟩

theorem weightedHeatRow_variable_measurable (k : ℕ) (Λ : ℝ) (q r : X → ℝ)
    (hq : Measurable q) (hr : Measurable r) :
    Measurable (fun z : (X × History P k) × HeatCircle =>
      weightedHeatRow Λ ((carrier L k).observations.observations z.1.2) (q z.1.1) (r z.1.1) z.2) := by
  have hrow : Measurable (fun z : (X × History P k) × HeatCircle =>
      heatRow ((carrier L k).observations.observations z.1.2) (r z.1.1) z.2) :=
    (carrier L k).observations.heatRow_measurable.comp
      (measurable_fst.snd.prodMk ((hr.comp measurable_fst.fst).prodMk measurable_snd))
  apply (WithLp.measurable_toLp 2 (Fin (n+k) → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hw : Measurable (fun z : (X × History P k) × HeatCircle =>
      weights Λ ((carrier L k).observations.observations z.1.2) (q z.1.1) i) := Real.measurable_exp.comp
    (((((carrier L k).observations.stop_measurable i).comp measurable_fst.snd).sub
      (hq.comp measurable_fst.fst)).const_mul (-Λ))
  have hi := hw.mul ((measurable_pi_apply i).comp
    ((WithLp.measurable_ofLp 2 (Fin (n+k) → ℝ)).comp hrow))
  convert! hi using 1
  funext z
  exact diagonal_apply _ _ i

attribute [local irreducible] cappedAverage weightedPoint

/-- True joint Borel dependence, including independent law and row times.
No score-range or ellipticity assumption is used for measurability. -/
theorem weightedPoint_variable_measurable (k : ℕ) (Λ : ℝ) (q r : X → ℝ)
    (hq : Measurable q) (hr : Measurable r)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2)) :
    Measurable (fun z : (X × History P k) × HeatCircle =>
      weightedPoint L k Λ (q z.1.1) (r z.1.1) (m z.1.1) z.1.2 z.2) := by
  classical
  have hp : Measurable (fun z : (X × History P k) × HeatCircle =>
      ((q z.1.1,z.1.2),m z.1.1 z.1.2)) :=
    ((hq.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk (hm.comp measurable_fst)
  have hd := (cappedAverage_fderiv_joint_measurable L k).comp hp
  have hv := (continuous_fst.clm_apply continuous_snd).measurable.comp
    (hd.prodMk (weightedHeatRow_variable_measurable L k Λ q r hq hr))
  have hs : MeasurableSet {z : (X × History P k) × HeatCircle |
      q z.1.1 < (carrier L k).terminal z.1.2 ∧ r z.1.1 < (carrier L k).terminal z.1.2} :=
    (measurableSet_lt (hq.comp measurable_fst.fst) ((carrier L k).terminal_measurable.comp measurable_fst.snd)).inter
      (measurableSet_lt (hr.comp measurable_fst.fst) ((carrier L k).terminal_measurable.comp measurable_fst.snd))
  have hh : Measurable (fun z : (X × History P k) × HeatCircle =>
      if q z.1.1 < (carrier L k).terminal z.1.2 ∧ r z.1.1 < (carrier L k).terminal z.1.2 then
        fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
          (weightedHeatRow Λ ((carrier L k).observations.observations z.1.2) (q z.1.1) (r z.1.1) z.2)
      else (0:ℝ)) := hv.ite hs measurable_const
  convert! hh using 1
  funext z
  simp only [weightedPoint]
  split_ifs with hb
  · simp only [cappedAverage,min_eq_left hb.1.le]
  · rfl

theorem weightedSpatial_variable_measurable (k : ℕ) (Λ : ℝ) (q r : X → ℝ)
    (hq : Measurable q) (hr : Measurable r)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (fun z : X × (HeatCircle × P) =>
      weightedSpatial L k Λ (q z.1) (r z.1) m (t z.1) z.1 z.2.1 z.2.2) := by
  have hp : Measurable (fun z : (X × (HeatCircle × P)) × (Fin k → HeatCircle) =>
      separated k (z.1.2.2,t z.1.1,z.2)) :=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      ((ht.comp measurable_fst.fst).prodMk measurable_snd))
  have hi := ((weightedPoint_variable_measurable L k Λ q r hq hr m hm).comp
    ((measurable_fst.fst.prodMk hp).prodMk measurable_fst.snd.fst)).stronglyMeasurable.integral_prod_right'
      (ν:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
  exact Complex.continuous_ofReal.measurable.comp hi.measurable

end SHE.ActualMeanKernel
