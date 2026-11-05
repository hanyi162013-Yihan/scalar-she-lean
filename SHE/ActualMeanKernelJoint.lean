module

public import SHE.ActualMeanKernelTrace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders
local instance actualMeanKernelJoint_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)
attribute [local irreducible] cappedAverage point

/-- The actual capped Gaussian average is jointly Borel in terminal
time, physical history and state, including every covariance rank change. -/
theorem cappedAverage_joint_measurable (k : ℕ) :
    Measurable (fun z : (ℝ × History P k) × WordRecursion.State (n+k) =>
      cappedAverage L k z.1.1 z.1.2 z.2) := by
  let Z := reindexFamily (carrier L k).observations (Prod.snd : ℝ × History P k → History P k) measurable_snd
  have hT := (carrier L k).terminal_measurable.comp
    (measurable_snd : Measurable (Prod.snd : ℝ × History P k → History P k))
  have hC := Z.covariance_measurable (R.reference_measurable.comp measurable_snd)
    (measurable_fst.min hT) hT (fun _ => min_le_right _ _)
  let A := fun z : (ℝ × History P k) × WordRecursion.State (n+k) => covariance R.reference
    ((carrier L k).observations.observations z.1.2)
    (min z.1.1 ((carrier L k).terminal z.1.2)) ((carrier L k).terminal z.1.2)
  have hA : Measurable A := hC.comp measurable_fst
  have hF : Measurable (fun z : ((ℝ × History P k) × WordRecursion.State (n+k)) × WordRecursion.State (n+k) =>
      UncutSmoothWords.test L k z.1.1.2 (z.1.2+z.2)) :=
    (UncutSmoothWords.test_measurable L k).comp
      (measurable_fst.fst.snd.prodMk (measurable_fst.snd.add measurable_snd))
  unfold cappedAverage
  exact (hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=GaussianScoreKernel.gaussianKernel A hA)).measurable

theorem cappedAverage_fderiv_joint_measurable (k : ℕ) :
    Measurable (fun z : (ℝ × History P k) × WordRecursion.State (n+k) =>
      fderiv ℝ (cappedAverage L k z.1.1 z.1.2) z.2) :=
  MeasurableDerivatives.fderiv_measurable (n:=n+k)
    (F:=fun z : ℝ × History P k => cappedAverage L k z.1 z.2)
    (cappedAverage_joint_measurable L k)
    (fun z => cappedAverage_differentiable L k z.1 z.2)

/-- The literal terminal derivative admits arbitrary measurable time and
current-mean substitutions. In particular the parameter sigma algebra may
be a predictable sigma algebra, rather than a Borel product. -/
theorem point_variable_measurable (k : ℕ) (q : X → ℝ) (hq : Measurable q)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2)) :
    Measurable (fun z : (X × History P k) × HeatCircle =>
      point L k (q z.1.1) (m z.1.1) z.1.2 z.2) := by
  classical
  have hf : Measurable (fun z : (ℝ × History P k) × WordRecursion.State (n+k) =>
      fderiv ℝ (cappedAverage L k z.1.1 z.1.2) z.2) :=
    cappedAverage_fderiv_joint_measurable L k
  have hp : Measurable (fun z : (X × History P k) × HeatCircle =>
      ((q z.1.1,z.1.2),m z.1.1 z.1.2)) :=
    ((hq.comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk (hm.comp measurable_fst)
  have hd : Measurable (fun z : (X × History P k) × HeatCircle =>
      fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)) :=
    hf.comp hp
  have hr : Measurable (fun z : (X × History P k) × HeatCircle =>
      heatRow ((carrier L k).observations.observations z.1.2) (q z.1.1) z.2) :=
    (carrier L k).observations.heatRow_measurable.comp
    (measurable_fst.snd.prodMk ((hq.comp measurable_fst.fst).prodMk measurable_snd))
  have hv : Measurable (fun z : (X × History P k) × HeatCircle =>
      fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
        (heatRow ((carrier L k).observations.observations z.1.2) (q z.1.1) z.2)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hd.prodMk hr)
  have hs : MeasurableSet {z : (X × History P k) × HeatCircle |
      q z.1.1 < (carrier L k).terminal z.1.2} :=
    measurableSet_lt (hq.comp measurable_fst.fst) ((carrier L k).terminal_measurable.comp measurable_fst.snd)
  have hh : Measurable (fun z : (X × History P k) × HeatCircle =>
      if q z.1.1 < (carrier L k).terminal z.1.2 then
        fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
          (heatRow ((carrier L k).observations.observations z.1.2) (q z.1.1) z.2) else (0:ℝ)) :=
    hv.ite hs measurable_const
  have he : (fun z : (X × History P k) × HeatCircle =>
      point L k (q z.1.1) (m z.1.1) z.1.2 z.2)=
      fun z => if q z.1.1 < (carrier L k).terminal z.1.2 then
        fderiv ℝ (cappedAverage L k (q z.1.1) z.1.2) (m z.1.1 z.1.2)
          (heatRow ((carrier L k).observations.observations z.1.2) (q z.1.1) z.2) else 0 := by
    funext z
    simp only [point]
    split_ifs with hb
    · simp only [cappedAverage,min_eq_left hb.le]
    · rfl
  rw [he]
  exact hh

/-- Joint measurable time/history substitution for the actual old-space
average. No sectionwise measurability premise is left. -/
theorem spatial_variable_measurable (k : ℕ) (q : X → ℝ) (hq : Measurable q)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (fun z : X × (HeatCircle × P) => spatial L k (q z.1) m (t z.1) z.1 z.2.1 z.2.2) := by
  have hp : Measurable (fun z : (X × (HeatCircle × P)) × (Fin k → HeatCircle) =>
      separated k (z.1.2.2,t z.1.1,z.2)) :=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      ((ht.comp measurable_fst.fst).prodMk measurable_snd))
  have hi := ((point_variable_measurable L k q hq m hm).comp
    ((measurable_fst.fst.prodMk hp).prodMk measurable_fst.snd.fst)).stronglyMeasurable.integral_prod_right'
      (ν:=Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
  exact Complex.continuous_ofReal.measurable.comp hi.measurable

end SHE.ActualMeanKernel
