module

public import SHE.SeparatedMeanOperator
public import SHE.NativeHeatComparable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers NormalizedKernelSplit NativeRandomKernel
local instance quarterKernelTimes_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R StoppedFourier.HeatCircle n)

def quarterGap (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) : ℝ :=
  max (fixedTerminal (R:=R) T k t-q) 0

def quarterRowTime (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) : ℝ :=
  q+quarterGap (R:=R) T k q t/4

def quarterTraceTime (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) : ℝ :=
  quarterGap (R:=R) T k q t/2

theorem fixedTerminal_continuous (T : ℝ) (k : ℕ) : Continuous (fixedTerminal (R:=R) T k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    change Continuous (fun t : Fin (k+1) → ℝ => max R.base
      (min (fixedTerminal (R:=R) T k (fun i => t i.succ)) (t 0)))
    exact continuous_const.max ((ih.comp (continuous_pi (fun i => continuous_apply i.succ))).min (continuous_apply 0))

theorem quarterGap_nonneg (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) :
    0 ≤ quarterGap (R:=R) T k q t := le_max_right _ _

theorem quarterTraceTime_nonneg (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ) :
    0 ≤ quarterTraceTime (R:=R) T k q t := div_nonneg (quarterGap_nonneg T k q t) (by norm_num)

theorem quarter_geometry (T : ℝ) (k : ℕ) (q : ℝ) (t : Fin k → ℝ)
    (hq : q < fixedTerminal (R:=R) T k t) :
    quarterGap (R:=R) T k q t=fixedTerminal (R:=R) T k t-q ∧
      q < quarterRowTime (R:=R) T k q t ∧
      quarterRowTime (R:=R) T k q t < fixedTerminal (R:=R) T k t ∧
      0 < quarterTraceTime (R:=R) T k q t ∧
      quarterTraceTime (R:=R) T k q t ≤ fixedTerminal (R:=R) T k t-quarterRowTime (R:=R) T k q t ∧
      2*(quarterRowTime (R:=R) T k q t-q)=quarterTraceTime (R:=R) T k q t := by
  have hg : quarterGap (R:=R) T k q t=fixedTerminal (R:=R) T k t-q := max_eq_left (sub_pos.mpr hq).le
  refine ⟨hg,?_⟩
  simp only [quarterRowTime,quarterTraceTime,hg]
  exact ⟨by linarith,by linarith,by linarith,by linarith,by ring⟩

theorem quarter_widths {T A q : ℝ} {k : ℕ} {t : Fin k → ℝ}
    (hq : q < fixedTerminal (R:=R) T k t) (hA : fixedTerminal (R:=R) T k t ≤ A) :
    let r := quarterRowTime (R:=R) T k q t
    0 < A-r ∧ A-r ≤ A-q ∧ A-q ≤ 2*(A-r) ∧
      quarterTraceTime (R:=R) T k q t ≤ A-r := by
  intro r
  have hg := (quarter_geometry T k q t hq).1
  dsimp only [r,quarterRowTime,quarterTraceTime]
  rw [hg]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem quarter_heat_envelope {T A q : ℝ} {k : ℕ} {t : Fin k → ℝ}
    (hq : q < fixedTerminal (R:=R) T k t) (hA : fixedTerminal (R:=R) T k t ≤ A)
    (a y : HeatCircle) :
    ‖ProfileVariance.heatPhysical (8*(A-quarterRowTime (R:=R) T k q t)) a y‖ ≤
      Real.sqrt 2*‖ProfileVariance.heatPhysical (8*(A-q)) a y‖ := by
  obtain ⟨hp,hle,hcomp,_⟩ := quarter_widths hq hA
  exact NativeHeatSpan.physical_comparable (by positivity : 0 < 8*(A-quarterRowTime (R:=R) T k q t))
    (by linarith) (by linarith) a y

theorem quarterRowTime_measurable (T : ℝ) (k : ℕ) {q : X → ℝ} (hq : Measurable q)
    {t : X → Fin k → ℝ} (ht : Measurable t) :
    Measurable (fun x => quarterRowTime (R:=R) T k (q x) (t x)) :=
  hq.add (((((fixedTerminal_continuous (R:=R) T k).measurable.comp ht).sub hq).max measurable_const).div_const 4)

theorem quarterTraceTime_measurable (T : ℝ) (k : ℕ) {q : X → ℝ} (hq : Measurable q)
    {t : X → Fin k → ℝ} (ht : Measurable t) :
    Measurable (fun x => quarterTraceTime (R:=R) T k (q x) (t x)) :=
  (((((fixedTerminal_continuous (R:=R) T k).measurable.comp ht).sub hq).max measurable_const).div_const 2)

/-- Every inactive time is genuinely zero; no exceptional-set or
unproved semigroup convention is needed for the global extension. -/
theorem quarter_operator_split (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (x : X) :
    integralOperator (field L k q m t) x=
      (integralOperator (rowField L k q (quarterRowTime (R:=R) T k q t) m t) x).comp
        (circleHeatOperator (quarterTraceTime (R:=R) T k q t/2)
          (div_nonneg (quarterTraceTime_nonneg T k q t) (by norm_num))) := by
  by_cases hq : q < fixedTerminal (R:=R) T k t
  · obtain ⟨_,hqr,hr,_,_,he⟩ := quarter_geometry T k q t hq
    have hh := row_operator_split L T hT k q (quarterRowTime (R:=R) T k q t) m hm t hqr.le hr x
    have ht : quarterTraceTime (R:=R) T k q t/2=quarterRowTime (R:=R) T k q t-q := by linarith
    simpa only [ht] using hh
  · have hg : quarterGap (R:=R) T k q t=0 := max_eq_right (sub_nonpos.mpr (le_of_not_gt hq))
    have hrow : quarterRowTime (R:=R) T k q t=q := by simp only [quarterRowTime,hg,zero_div,add_zero]
    have hz : field L k q m t=0 := by
      funext z
      have hbad : ¬ q < (carrier L k).terminal (HistoryProductMeasure.separated k (z.2.2,t,fun _ => (0:HeatCircle))) := by
        simpa only [terminal_separated L T hT] using hq
      simp only [field,spatial,point,terminal_separated L T hT,if_neg hq,integral_zero,Complex.ofReal_zero,Pi.zero_apply]
    have hrowzero : rowField L k q (quarterRowTime (R:=R) T k q t) m t=0 := by rw [hrow,rowField_same,hz]
    rw [hz,hrowzero]
    have hOp : integralOperator (0 : X × Space → ℂ) x=0 := by
      apply ContinuousLinearMap.ext
      intro v
      apply Lp.ext
      filter_upwards [NativeRandomKernel.integralOperator_ae (F:=0) measurable_const le_rfl
        (fun _ _ _ => by simp) x v,Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=AddCircle.haarAddCircle (T:=2*Real.pi))] with y hy hz
      change integralOperator (0 : X × Space → ℂ) x v y=(0:CircleL2) y
      rw [hz]
      simpa only [Pi.zero_apply,zero_mul,integral_zero] using hy
    simp only [hOp,ContinuousLinearMap.zero_comp]

end SHE.ActualMeanKernel
