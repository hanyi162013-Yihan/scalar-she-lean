module

public import SHE.HistorySpatialSections
public import SHE.PhysicalParentGeometry
public import SHE.PredictablePhysicalFields
public import SHE.ControlledFutureFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers GaussianConvolution HistoryProductMeasure
  SmoothCylinders PhysicalParentGeometry
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T := 2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P Ω : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The genuine terminal derivative in a physical point heat-row direction.
The zero extension records its actual time domain explicitly. -/
def point (k : ℕ) (q : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) : ℝ :=
  if q < (carrier L k).terminal p then
    fderiv ℝ (gaussianAverage (covariance R.reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (m p)
      (heatRow ((carrier L k).observations.observations p) q y)
  else 0

/-- Literal spatial-history averaged mean kernel. Original history times
are fixed here; the time integration belongs to the later time ledger. -/
def spatial (k : ℕ) (q : ℝ) (m : Ω → History P k → WordRecursion.State (n+k))
    (t : Fin k → ℝ) (ω : Ω) (y : HeatCircle) (p : P) : ℂ :=
  ((∫ x : Fin k → HeatCircle,
    point L k q (m ω) (separated k (p,t,x)) y
    ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) : ℝ)

/-- The manuscript's compensated conditional mean, with every original
physical target and center retained. -/
def controlledMean (k : ℕ) (Λ q : ℝ) (hq : 0 ≤ q)
    (u d : CircleL2) (Z D : Ω → CircleL2) (θ : ℝ) (ω : Ω) (p : History P k) : WordRecursion.State (n+k) :=
  ControlledFutureMeans.futureMeanVector Λ
    (fun i => ((carrier L k).observations.observations p i).target)
    (fun i => NativeHeatSpan.unitCenter (((carrier L k).observations.observations p i).center))
    q hq u d (Z ω) (D ω) θ

theorem point_of_before (k : ℕ) (q : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) (hq : q < (carrier L k).terminal p) :
    point L k q m p y =
      fderiv ℝ (gaussianAverage (covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) (m p)
        (heatRow ((carrier L k).observations.observations p) q y) := by
  simp only [point,if_pos hq]

theorem point_zero_of_not_strict (k : ℕ) (q : ℝ) (m : History P k → WordRecursion.State (n+k))
    (p : History P k) (y : HeatCircle) (hp : ¬ StrictHistory L k p) :
    point L k q m p y = 0 := by
  simp only [point,test_zero_of_not_strict L k p hp]
  have hz (A : Matrix (Fin (n+k)) (Fin (n+k)) ℝ) :
      gaussianAverage A (0 : WordRecursion.State (n+k) → ℝ) = fun _ => 0 := by
    funext z
    simp [gaussianAverage]
  have hd : fderiv ℝ (fun _ : WordRecursion.State (n+k) => (0:ℝ)) (m p) = 0 :=
    (hasFDerivAt_const (0:ℝ) (m p)).fderiv
  simp only [hz,hd,ContinuousLinearMap.zero_apply,ite_self]

/-- All finite uncut tests are genuinely bounded smooth in the state.
The bounds may depend on the fixed physical history. -/
theorem test_boundedSmooth (k : ℕ) (p : History P k) :
    BoundedSmooth (UncutSmoothWords.test L k p) := by
  rw [UncutSmoothWords.test_eq_weight_normalized]
  change BoundedSmooth (fun z => UncutSmoothWords.weight L k p * UncutSmoothWords.normalized L k p z)
  exact (BoundedSmooth.const (UncutSmoothWords.weight L k p)).mul
      ((UncutSmoothWords.normalized_uniform L k).boundedSmooth p)

/-- A harmless capped extension makes the average Borel on all histories;
on the actual domain q < terminal it is exactly the original average. -/
def cappedAverage (k : ℕ) (q : ℝ) (p : History P k) : WordRecursion.State (n+k) → ℝ :=
  gaussianAverage (covariance R.reference ((carrier L k).observations.observations p)
    (min q ((carrier L k).terminal p)) ((carrier L k).terminal p))
    (UncutSmoothWords.test L k p)

theorem cappedAverage_measurable (k : ℕ) (q : ℝ) :
    Measurable (fun p : History P k × WordRecursion.State (n+k) => cappedAverage L k q p.1 p.2) := by
  have hC := (carrier L k).observations.covariance_measurable
    (R.reference_measurable.comp measurable_snd)
    ((measurable_const (a := q)).min (carrier L k).terminal_measurable)
    (carrier L k).terminal_measurable (fun _ => min_le_right _ _)
  let A := fun p : History P k × WordRecursion.State (n+k) => covariance R.reference
    ((carrier L k).observations.observations p.1)
    (min q ((carrier L k).terminal p.1)) ((carrier L k).terminal p.1)
  have hA : Measurable A := hC.comp measurable_fst
  have hF : Measurable (fun p : (History P k × WordRecursion.State (n+k)) × WordRecursion.State (n+k) =>
      UncutSmoothWords.test L k p.1.1 (p.1.2+p.2)) :=
    (UncutSmoothWords.test_measurable L k).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.add measurable_snd))
  exact (hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ := GaussianScoreKernel.gaussianKernel A hA)).measurable

theorem cappedAverage_differentiable (k : ℕ) (q : ℝ) (p : History P k) :
    Differentiable ℝ (cappedAverage L k q p) :=
  ((test_boundedSmooth L k p).average (multivariateGaussian 0 _)).smooth.differentiable (by simp)


variable [MeasurableSpace Ω]

/-- Joint Borel dependence of the literal physical point kernel, with a
possibly random and history-dependent current mean. -/
theorem point_measurable (k : ℕ) (q : ℝ)
    (m : Ω → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2)) :
    Measurable (fun z : (Ω × History P k) × HeatCircle =>
      point L k q (m z.1.1) z.1.2 z.2) := by
  classical
  have hp : Measurable (fun z : (Ω × History P k) × HeatCircle => z.1.2) := measurable_fst.snd
  have hd := (MeasurableDerivatives.fderiv_measurable (cappedAverage_measurable L k q)
    (cappedAverage_differentiable L k q)).comp (hp.prodMk (hm.comp measurable_fst))
  have hr := (carrier L k).observations.heatRow_measurable.comp
    (hp.prodMk ((measurable_const (a := q)).prodMk measurable_snd))
  have hv : Measurable (fun z : (Ω × History P k) × HeatCircle =>
      fderiv ℝ (cappedAverage L k q z.1.2) (m z.1.1 z.1.2)
        (heatRow ((carrier L k).observations.observations z.1.2) q z.2)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hd.prodMk hr)
  have hs : MeasurableSet {z : (Ω × History P k) × HeatCircle |
      q < (carrier L k).terminal z.1.2} :=
    measurableSet_lt (measurable_const (a := q)) ((carrier L k).terminal_measurable.comp hp)
  have hh : Measurable (fun z : (Ω × History P k) × HeatCircle =>
      if q < (carrier L k).terminal z.1.2 then
        fderiv ℝ (cappedAverage L k q z.1.2) (m z.1.1 z.1.2)
          (heatRow ((carrier L k).observations.observations z.1.2) q z.2)
      else 0) := hv.ite hs measurable_const
  convert! hh using 1
  funext z
  simp only [point]
  split_ifs with hq
  · simp only [cappedAverage,min_eq_left hq.le]
  · rfl

/-- The actual old-space integral is jointly Borel in the random outcome,
physical input point and original output/root parameter. -/
theorem spatial_measurable (k : ℕ) (q : ℝ)
    (m : Ω → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2)) (t : Fin k → ℝ) :
    Measurable (fun z : Ω × (HeatCircle × P) => spatial L k q m t z.1 z.2.1 z.2.2) := by
  have hp : Measurable (fun z : (Ω × (HeatCircle × P)) × (Fin k → HeatCircle) =>
      separated k (z.1.2.2,t,z.2)) :=
    (separated_measurable k).comp (measurable_fst.snd.snd.prodMk
      (measurable_const.prodMk measurable_snd))
  have hi := ((point_measurable L k q m hm).comp
    ((measurable_fst.fst.prodMk hp).prodMk measurable_fst.snd.fst)).stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle))
  exact Complex.continuous_ofReal.measurable.comp hi.measurable


set_option backward.isDefEq.respectTransparency false in
/-- The literal compensated current mean is Borel even outside the active
time domain. Thus its zero-extended physical kernel uses a genuine joint
Borel function, without any choice of pointwise representatives. -/
theorem controlledMean_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    (k : ℕ) (Λ q : ℝ) (hq : 0 ≤ q) (u d : CircleL2)
    (Z D : Ω → CircleL2) (hZ : Measurable Z) (hD : Measurable D) (θ : ℝ) :
    Measurable (fun z : Ω × History P k => controlledMean L k Λ q hq u d Z D θ z.1 z.2) := by
  unfold controlledMean ControlledFutureMeans.futureMeanVector
  apply (WithLp.measurable_toLp 2 (Fin (n+k) → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT : Measurable (fun z : Ω × History P k =>
      ((carrier L k).observations.observations z.2 i).target) :=
    ((carrier L k).observations.target_measurable i).comp measurable_snd
  have hx : Measurable (fun z : Ω × History P k => StoppedGaussianScore.nativeCenter
      (fun j => NativeHeatSpan.unitCenter (((carrier L k).observations.observations z.2 j).center)) i) := by
    simpa only [StoppedGaussianScore.nativeCenter,NativeHeatSpan.scale_inverse,Function.comp_def] using
      (((carrier L k).observations.center_measurable i).comp
        (measurable_snd : Measurable (Prod.snd : Ω × History P k → History P k)))
  have hage := (hT.sub_const q).prodMk hx
  have hlin : Measurable (fun z : CircleL2 × CircleL2 => z.1 + θ • z.2) := by
    have hθ : Continuous (fun _ : CircleL2 × CircleL2 => θ) := continuous_const
    convert! (continuous_fst.add (hθ.smul continuous_snd)).measurable using 1
  have hstate := hlin.comp (hZ.prodMk hD)
  have hcur := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hstate.comp measurable_fst).prodMk hage)
  have hbase := (ControlledProfile.mean_measurable Λ u d).comp
    ((measurable_const (a := θ)).prodMk (hT.prodMk hx))
  have href := (PhysicalProfile.physicalHeatMean_measurable
    (ControlledFutureMeans.referenceState Λ q hq u d θ)).comp hage
  exact (hcur.add hbase).sub href

end SHE.ActualMeanKernel
