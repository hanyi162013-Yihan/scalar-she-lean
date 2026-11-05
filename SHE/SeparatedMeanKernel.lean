module

public import SHE.ActualMeanKernelJoint
public import SHE.ActualMeanPointBounds
public import SHE.FiniteHeatRows

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders
local instance separatedMeanKernel_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Gaussian covariance and current mean remain at q; only the physical
direction row is evaluated at r. The harmless inactive extension also
vanishes when r is outside the terminal interval. -/
def rowPoint (k : ℕ) (q r : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) : ℝ :=
  if q < (carrier L k).terminal p ∧ r < (carrier L k).terminal p then
    fderiv ℝ (gaussianAverage (covariance R.reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (m p)
      (heatRow ((carrier L k).observations.observations p) r y)
  else 0

def rowSpatial (k : ℕ) (q r : ℝ) (m : X → History P k → WordRecursion.State (n+k))
    (t : Fin k → ℝ) (x : X) (y : HeatCircle) (p : P) : ℂ :=
  ((∫ z : Fin k → HeatCircle,rowPoint L k q r (m x) (separated k (p,t,z)) y
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ)

theorem rowPoint_same (k : ℕ) (q : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) : rowPoint L k q q m p y=point L k q m p y := by
  simp only [rowPoint,point,and_self]

theorem rowSpatial_same (k : ℕ) (q : ℝ)
    (m : X → History P k → WordRecursion.State (n+k)) (t : Fin k → ℝ) :
    rowSpatial L k q q m t=spatial L k q m t := by
  funext x y p
  simp only [rowSpatial,spatial,rowPoint_same]

theorem rowPoint_of_active (k : ℕ) (q r : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle)
    (hq : q < (carrier L k).terminal p) (hr : r < (carrier L k).terminal p) :
    rowPoint L k q r m p y=
      fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) (m p)
        (heatRow ((carrier L k).observations.observations p) r y) := by
  unfold rowPoint
  exact if_pos ⟨hq,hr⟩

attribute [local irreducible] cappedAverage rowPoint

/-- Genuine separate q/r joint measurability, retaining the actual q-law
and q-current mean throughout. -/
theorem rowPoint_variable_measurable (k : ℕ) (q r : X → ℝ) (hq : Measurable q) (hr : Measurable r)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2)) :
    Measurable (fun z : (X × History P k) × HeatCircle =>
      rowPoint L k (q z.1.1) (r z.1.1) (m z.1.1) z.1.2 z.2) := by
  classical
  have hp : Measurable (fun z : (X × History P k) × HeatCircle =>
      ((q z.1.1,z.1.2),m z.1.1 z.1.2)) :=
    ((hq.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk (hm.comp measurable_fst)
  have hd : Measurable (fun z : (X × History P k) × HeatCircle =>
      fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)) :=
    (cappedAverage_fderiv_joint_measurable L k).comp hp
  have hrow : Measurable (fun z : (X × History P k) × HeatCircle =>
      heatRow ((carrier L k).observations.observations z.1.2) (r z.1.1) z.2) :=
    (carrier L k).observations.heatRow_measurable.comp
      (measurable_fst.snd.prodMk ((hr.comp measurable_fst.fst).prodMk measurable_snd))
  have hv : Measurable (fun z : (X × History P k) × HeatCircle =>
      fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
        (heatRow ((carrier L k).observations.observations z.1.2) (r z.1.1) z.2)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hd.prodMk hrow)
  have hs : MeasurableSet {z : (X × History P k) × HeatCircle |
      q z.1.1 < (carrier L k).terminal z.1.2 ∧ r z.1.1 < (carrier L k).terminal z.1.2} :=
    (measurableSet_lt (hq.comp measurable_fst.fst) ((carrier L k).terminal_measurable.comp measurable_fst.snd)).inter
      (measurableSet_lt (hr.comp measurable_fst.fst) ((carrier L k).terminal_measurable.comp measurable_fst.snd))
  have hh : Measurable (fun z : (X × History P k) × HeatCircle =>
      if q z.1.1 < (carrier L k).terminal z.1.2 ∧ r z.1.1 < (carrier L k).terminal z.1.2 then
        fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
          (heatRow ((carrier L k).observations.observations z.1.2) (r z.1.1) z.2) else (0:ℝ)) :=
    hv.ite hs measurable_const
  convert! hh using 1
  funext z
  simp only [rowPoint]
  split_ifs with hb
  · simp only [cappedAverage,min_eq_left hb.1.le]
  · rfl

theorem rowSpatial_variable_measurable (k : ℕ) (q r : X → ℝ) (hq : Measurable q) (hr : Measurable r)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (fun z : X × (HeatCircle × P) => rowSpatial L k (q z.1) (r z.1) m (t z.1) z.1 z.2.1 z.2.2) := by
  have hp : Measurable (fun z : (X × (HeatCircle × P)) × (Fin k → HeatCircle) =>
      separated k (z.1.2.2,t z.1.1,z.2)) :=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      ((ht.comp measurable_fst.fst).prodMk measurable_snd))
  have hi := ((rowPoint_variable_measurable L k q r hq hr m hm).comp
    ((measurable_fst.fst.prodMk hp).prodMk measurable_fst.snd.fst)).stronglyMeasurable.integral_prod_right'
      (ν:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
  exact Complex.continuous_ofReal.measurable.comp hi.measurable

end SHE.ActualMeanKernel
