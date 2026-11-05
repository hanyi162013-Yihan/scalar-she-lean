module

public import SHE.StopWeightedInput

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure PhysicalMeanRange
open scoped ENNReal
local instance weightedMeanInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
variable {P X : Type} [MeasurableSpace P] [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- Exact physical current-mean mark as a signed spatial input against
the literal stop-weighted q-law kernel. The input may be random and
dependent on every root/leaf Gaussian mean. -/
theorem weightedPoint_mean_input (k : ℕ) (Λ q : ℝ)
    (m : History P k→WordRecursion.State (n+k)) (p : History P k)
    (hq : q<(carrier L k).terminal p) (v : CircleL2) :
    let Z := (carrier L k).observations.observations p
    fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal p))
      (UncutSmoothWords.test L k p)) (m p)
      (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
        (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ v)=
      ∫ y : HeatCircle,weightedPoint L k Λ q q m p y*(v y).re ∂haarAddCircle := by
  let Z := (carrier L k).observations.observations p
  let D := fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal p))
    (UncutSmoothWords.test L k p)) (m p)
  have hr (i : Fin (n+k)) : q<(Z i).target := hq.trans_le ((carrier L k).targets_after p i)
  simpa only [weightedPoint_of_active L k Λ q q m p _ hq hq] using
    StopWeightedInput.dampedDirection_integral D Λ q Z hr v

/-- The actual old-space average is changed to the weighted-kernel
input integral only after genuine Bochner Fubini is proved. The finite
coarse bound pays no quantitative cost. -/
theorem weightedSpatial_mean_input (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q : ℝ)
    (m : X→History P k→WordRecursion.State (n+k))
    (hm : Measurable (fun z : X×History P k => m z.1 z.2)) (t : Fin k→ℝ)
    (hq : q<fixedTerminal (R:=R) T k t) (x : X) (p : P) (v : CircleL2) :
    (∫ y : HeatCircle,weightedSpatial L k Λ q q m t x y p*v y ∂haarAddCircle).re=
      ∫ z : Fin k→HeatCircle,
        let a := separated k (p,t,z)
        let Z := (carrier L k).observations.observations a
        fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal a))
          (UncutSmoothWords.test L k a)) (m x a)
          (dampedDirection (fun i=>(Z i).stop) (fun i=>(Z i).target)
            (fun i=>NativeHeatSpan.unitCenter (Z i).center) q Λ v)
        ∂Measure.pi (fun _ => haarAddCircle) := by
  let ν := Measure.pi (fun _ : Fin k => (haarAddCircle (T:=2*π)))
  let F : (Fin k→HeatCircle)×HeatCircle→ℂ := fun z =>
    (weightedPoint L k Λ q q (m x) (separated k (p,t,z.1)) z.2:ℝ)
  have hsep : Measurable (fun z : (Fin k→HeatCircle)×HeatCircle => separated k (p,t,z.1)) :=
    (separated_measurable k).comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
  have hF : Measurable F := Complex.continuous_ofReal.measurable.comp
    ((weightedPoint_variable_measurable L k Λ (fun _ : X=>q) (fun _=>q) measurable_const measurable_const m hm).comp
      ((measurable_const.prodMk hsep).prodMk measurable_snd))
  obtain ⟨B,hB,hbound⟩ := weightedPoint_uniform_bound L (X:=X) T hT k hΛ q q t
  have hb (z : Fin k→HeatCircle) (y : HeatCircle) : ‖F (z,y)‖≤B := by
    simpa only [F,Complex.norm_real,Real.norm_eq_abs] using hbound m x y p z
  have hv : Integrable (v : HeatCircle→ℂ) haarAddCircle := (Lp.memLp v).integrable (by norm_num)
  have hi : Integrable (fun z : (Fin k→HeatCircle)×HeatCircle => F z*v z.2) (ν.prod haarAddCircle) := by
    apply ((hv.norm.const_mul B).comp_snd ν).mono'
      (hF.aestronglyMeasurable.mul hv.aestronglyMeasurable.comp_snd)
    exact ae_of_all _ (fun z => by
      change ‖F z*v z.2‖≤B*‖v z.2‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z.1 z.2) (norm_nonneg _))
  have hswap := KernelAverageFubini.integral_average_mul ν hF hB hb v
  have heq : (∫ y : HeatCircle,weightedSpatial L k Λ q q m t x y p*v y ∂haarAddCircle)=
      ∫ z : Fin k→HeatCircle,(∫ y : HeatCircle,F (z,y)*v y ∂haarAddCircle) ∂ν := by
    simpa only [weightedSpatial,F,ν,integral_complex_ofReal] using hswap
  rw [heq]
  change RCLike.re (∫ z : Fin k→HeatCircle,(∫ y : HeatCircle,F (z,y)*v y ∂haarAddCircle) ∂ν)=_
  rw [←integral_re hi.integral_prod_left]
  apply integral_congr_ae
  refine ae_of_all _ (fun z => ?_)
  let a := separated k (p,t,z)
  let Z := (carrier L k).observations.observations a
  let D := fderiv ℝ (gaussianAverage (covariance R.reference Z q ((carrier L k).terminal a))
    (UncutSmoothWords.test L k a)) (m x a)
  have hqa : q<(carrier L k).terminal a := by simpa only [a,terminal_separated L T hT] using hq
  have hr (i : Fin (n+k)) : q<(Z i).target := hqa.trans_le ((carrier L k).targets_after a i)
  have hpoint (y : HeatCircle) : F (z,y)=((D (StopWeightedRows.weightedHeatRow Λ Z q q y):ℝ):ℂ) := by
    simpa only [F,D,Z,a] using congrArg Complex.ofReal
      (weightedPoint_of_active L k Λ q q (m x) a y hqa hqa)
  simp_rw [hpoint]
  have hfun : FiniteHeatRows.functional (D.comp (StopWeightedRows.diagonal (StopWeightedRows.weights Λ Z q))) Z q v=
      ∫ y : HeatCircle,((D (StopWeightedRows.weightedHeatRow Λ Z q q y):ℝ):ℂ)*v y ∂haarAddCircle := by
    simpa only [ContinuousLinearMap.comp_apply,StopWeightedRows.weightedHeatRow] using
      FiniteHeatRows.functional_integral (D.comp (StopWeightedRows.diagonal (StopWeightedRows.weights Λ Z q))) Z hr v
  rw [←hfun]
  exact (StopWeightedInput.functional_dampedDirection D Λ q Z hr v).symm

end SHE.ActualMeanKernel
