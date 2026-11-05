module

public import SHE.CutoffWordAnalytic
public import SHE.JointWordObserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointWordAnalytic
open Set MeasureTheory StoppedFourier WordRecursion CovarianceEndpoint GaussianItoTest
open CutoffWordLevel VariableObservations CutoffWordAnalytic
open Classical
abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

def state (p : P) (ω : Ω) (t : ℝ) : State n := JointWordObserve.evaluate Λ
  (fun s => U (ω,s)) (fun s => V (ω,s)) (fun q => XU (ω,q)) (fun q => XV (ω,q))
  (L.observations.observations p) t

def leaf (p : P) (ω : Ω) : ℝ := L.test p (state L Λ U V XU XV p ω (L.terminal p))
def reference (p : P) (ω : Ω) : ℝ :=
  backward (L.window p) (L.test p) R.base (state L Λ U V XU XV p ω R.base)

def insertion (p : P) (ω : Ω) (t : ℝ) (x : HeatCircle) : ℝ :=
  WordRecursion.insertion R.totalVariance R.reference (L.observations.observations p) t x
    (backward (L.window p) (L.test p) t)
    (JointPhysicalInsertion.appendState (XV (ω,(t,x))) (state L Λ U V XU XV p ω t))

def remainder (p : P) (ω : Ω) : ℝ :=
  ∫ t in R.base..L.terminal p,∫ x : HeatCircle,insertion L Λ U V XU XV p ω t x ∂AddCircle.haarAddCircle

variable {U V XU XV}
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
include hU hV hXU hXV

theorem state_measurable : Measurable (fun p : (P×Ω)×ℝ => state L Λ U V XU XV p.1.1 p.1.2 p.2) := by
  let Z : Family (P×Ω) n := reindexFamily L.observations Prod.fst measurable_fst
  exact JointWordObserve.evaluate_measurable Z Λ
    (hU.comp (measurable_fst.snd.prodMk measurable_snd))
    (hV.comp (measurable_fst.snd.prodMk measurable_snd))
    (hXU.comp (measurable_fst.snd.prodMk measurable_snd))
    (hXV.comp (measurable_fst.snd.prodMk measurable_snd))

theorem leaf_measurable : Measurable (fun p : P×Ω => leaf L Λ U V XU XV p.1 p.2) := by
  have hs := (state_measurable L Λ hU hV hXU hXV).comp
    (measurable_id.prodMk (L.terminal_measurable.comp measurable_fst))
  exact L.test_measurable.comp (measurable_fst.prodMk hs)

set_option backward.isDefEq.respectTransparency true in
theorem reference_measurable : Measurable (fun p : P×Ω => reference L Λ U V XU XV p.1 p.2) := by
  have hs := (state_measurable L Λ hU hV hXU hXV).comp
    (measurable_id.prodMk (measurable_const (a := R.base)))
  have hm : Measurable (fun p : P×Ω => ((p.1,R.base),state L Λ U V XU XV p.1 p.2 R.base)) :=
    ((measurable_fst.prodMk measurable_const).prodMk hs)
  have hc := (backward_measurable L).comp hm
  simpa only [Function.comp_def,reference] using hc

set_option backward.isDefEq.respectTransparency true in
theorem insertion_measurable :
    Measurable (fun p : ((P×Ω)×ℝ)×HeatCircle => insertion L Λ U V XU XV p.1.1.1 p.1.1.2 p.1.2 p.2) := by
  have hs := (state_measurable L Λ hU hV hXU hXV).comp
    (measurable_fst : Measurable (fun p : ((P×Ω)×ℝ)×HeatCircle => p.1))
  have hG : Measurable (fun p : (P×ℝ)×State n =>
      GaussianTaylor.hessian (backward (L.window p.1.1) (L.test p.1.1) p.1.2) p.2) :=
    MeasurableDerivatives.hessian_measurable (backward_measurable L)
      (fun p => ((backward_uniform L).smooth p).of_le (by simp))
  have hH := hG.comp ((measurable_fst.fst.fst.prodMk measurable_fst.snd).prodMk hs)
  have hrowMap : Measurable (fun p : ((P×Ω)×ℝ)×HeatCircle => (p.1.1.1,(p.1.2,p.2))) :=
    measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hrow := L.observations.heatRow_measurable.comp hrowMap
  have he₁ : Continuous (fun p : (State n→L[ℝ]State n→L[ℝ]ℝ)×State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have he₂ : Continuous (fun p : (State n→L[ℝ]ℝ)×State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hd := he₂.measurable.comp ((he₁.measurable.comp (hH.prodMk hrow)).prodMk hrow)
  have hc : Measurable (fun p : ((P×Ω)×ℝ)×HeatCircle =>
      R.totalVariance (XV (p.1.1.2,(p.1.2,p.2)))-R.reference (p.1.2,p.2)) :=
    (R.totalVariance_smooth.smooth.continuous.measurable.comp
      (hXV.comp (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd)))).sub
      (R.reference_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  convert (hc.const_mul (1/2:ℝ)).mul hd using 1
  funext p
  simp only [insertion,JointPhysicalInsertion.insertion_appendState,Function.comp_def,Pi.mul_apply]

theorem remainder_measurable : Measurable (fun p : P×Ω => remainder L Λ U V XU XV p.1 p.2) := by
  have hi := (insertion_measurable L Λ hU hV hXU hXV).stronglyMeasurable.integral_prod_right'
    (ν := AddCircle.haarAddCircle)
  have hm : Measurable (fun p : (P×Ω)×ℝ => if R.base<p.2 ∧ p.2≤L.terminal p.1.1 then
      ∫ x : HeatCircle,insertion L Λ U V XU XV p.1.1 p.1.2 p.2 x ∂AddCircle.haarAddCircle else 0) :=
    hi.measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (L.terminal_measurable.comp measurable_fst.fst))) measurable_const
  have ht := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert ht.measurable using 1
  funext p
  rw [remainder,intervalIntegral.integral_of_le (L.terminal_base p.1),← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator,mem_Ioc]

end SHE.JointWordAnalytic
