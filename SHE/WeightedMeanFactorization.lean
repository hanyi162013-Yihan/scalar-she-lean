module

public import SHE.WeightedMeanBounds
public import SHE.KernelAverageFubini

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders NormalizedKernelSplit
  StopWeightedRows
open scoped ENNReal
local instance weightedMeanFactorization_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance weightedMeanFactorization_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance weightedMeanFactorization_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The true weighted signed direction factors through later input heat
after old-space averaging. The stopping weights, covariance and current
mean all remain at q. -/
theorem weightedSpatial_integral_split (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q r : ℝ)
    (m : X → History P k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History P k => m z.1 z.2))
    (t : Fin k → ℝ) (hqr : q≤r) (hr : r<fixedTerminal (R:=R) T k t)
    (x : X) (p : P) (v : CircleL2) :
    (∫ y : HeatCircle,weightedSpatial L k Λ q q m t x y p*v y ∂haarAddCircle)=
      ∫ y : HeatCircle,weightedSpatial L k Λ q r m t x y p*
        circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v y ∂haarAddCircle := by
  let ν := Measure.pi (fun _ : Fin k => (haarAddCircle (T:=2*π)))
  let F := fun s : ℝ => fun z : (Fin k → HeatCircle) × HeatCircle =>
    ((weightedPoint L k Λ q s (m x) (separated k (p,t,z.1)) z.2:ℝ):ℂ)
  have hsep : Measurable (fun z : (Fin k → HeatCircle) × HeatCircle => separated k (p,t,z.1)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  have hFM (s : ℝ) : Measurable (F s) :=
    Complex.continuous_ofReal.measurable.comp
      ((weightedPoint_variable_measurable L k Λ (fun _ : X => q) (fun _ : X => s)
        measurable_const measurable_const m hm).comp
        ((measurable_const.prodMk hsep).prodMk measurable_snd))
  have hswap (s : ℝ) (w : CircleL2) :
      (∫ y : HeatCircle,weightedSpatial L k Λ q s m t x y p*w y ∂haarAddCircle)=
        ∫ z : Fin k → HeatCircle,(∫ y : HeatCircle,F s (z,y)*w y ∂haarAddCircle) ∂ν := by
    obtain ⟨B,hB,hbound⟩ := weightedPoint_uniform_bound L (X:=X) T hT k hΛ q s t
    have hb (z : Fin k → HeatCircle) (y : HeatCircle) : ‖F s (z,y)‖≤B := by
      simpa only [F,Complex.norm_real,Real.norm_eq_abs] using hbound m x y p z
    simpa only [weightedSpatial,F,ν,integral_complex_ofReal] using
      KernelAverageFubini.integral_average_mul ν (hFM s) hB hb w
  rw [hswap q v,hswap r (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v)]
  apply integral_congr_ae
  refine ae_of_all _ (fun z => ?_)
  let a := separated k (p,t,z)
  let Z := (carrier L k).observations.observations a
  let D := fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal a))
    (UncutSmoothWords.test L k a)) (m x a)
  let Dq := D.comp (diagonal (weights Λ Z q))
  have hterminal : (carrier L k).terminal a=fixedTerminal (R:=R) T k t := terminal_separated L T hT k t p z
  have hra : r<(carrier L k).terminal a := by simpa only [hterminal] using hr
  have hqa : q<(carrier L k).terminal a := hqr.trans_lt hra
  have hrZ (i : Fin (n+k)) : r<(Z i).target := hra.trans_le ((carrier L k).targets_after a i)
  have hqZ (i : Fin (n+k)) : q<(Z i).target := hqr.trans_lt (hrZ i)
  have hEq : (∫ y : HeatCircle,((Dq (heatRow Z q y):ℝ):ℂ)*v y ∂haarAddCircle)=
      ∫ y : HeatCircle,((Dq (heatRow Z r y):ℝ):ℂ)*
        circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v y ∂haarAddCircle := by
    rw [←FiniteHeatRows.functional_integral Dq Z hqZ v,
      ←FiniteHeatRows.functional_integral Dq Z hrZ (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v),
      FiniteHeatRows.functional_split Dq Z hqr hrZ]
    rfl
  simpa only [F,weightedPoint_of_active L k Λ q q (m x) a _ hqa hqa,
    weightedPoint_of_active L k Λ q r (m x) a _ hqa hra,Dq,ContinuousLinearMap.comp_apply,
    weightedHeatRow,D,Z,a] using hEq

end SHE.ActualMeanKernel
