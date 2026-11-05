module

public import SHE.PhysicalIto
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Borel dependence of actual physical observations and inserted words. -/
noncomputable section
namespace SHE.ObservationMeasurable
open Set MeasureTheory StoppedFourier WordRecursion PhysicalIto

abbrev State (n : ℕ) := WordRecursion.State n
variable {P : Type*} [MeasurableSpace P]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

theorem observe_joint_measurable {n : ℕ} (Z : Fin n → Observation)
    {U : P × ℝ → CircleL2} (hU : Measurable U) {X : P × (ℝ × HeatCircle) → ℝ}
    (hX : Measurable X) :
    Measurable (fun p : P × ℝ => observe (fun t => U (p.1, t)) (fun q => X (p.1, q)) Z p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hmean := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    (hU.prodMk (((measurable_const (a := (Z i).target)).sub measurable_snd).prodMk
      (measurable_const (a := (Z i).center))))
  have hstate := hX.comp (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const (a := (Z i).center))))
  exact hmean.ite (measurableSet_lt measurable_snd measurable_const) hstate

theorem stoppedObserve_joint_measurable {n : ℕ} (Z : Fin n → Observation)
    {U : P × ℝ → CircleL2} (hU : Measurable U) {X : P × (ℝ × HeatCircle) → ℝ}
    (hX : Measurable X) :
    Measurable (fun p : P × ℝ => stoppedObserve (fun t => U (p.1, t)) (fun q => X (p.1, q)) Z p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hr : Measurable (fun p : P × ℝ => min p.2 (Z i).stop) := measurable_snd.min measurable_const
  have hmean := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hU.comp (measurable_fst.prodMk hr)).prodMk
      (((measurable_const (a := (Z i).target)).sub hr).prodMk (measurable_const (a := (Z i).center))))
  have hstate := hX.comp (measurable_fst.prodMk (hr.prodMk (measurable_const (a := (Z i).center))))
  exact hmean.ite (measurableSet_lt hr measurable_const) hstate

theorem heatRow_joint_measurable {n : ℕ} (Z : Fin n → Observation) :
    Measurable (fun p : ℝ × HeatCircle => heatRow Z p.1 p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact Measurable.of_eval (CovarianceMatrix.heatRow_measurable Z)

theorem inserted_field_measurable {n : ℕ} (Z : Fin n → Observation)
    {U : P × ℝ → CircleL2} (hU : Measurable U) {X : P × (ℝ × HeatCircle) → ℝ} (hX : Measurable X)
    {a : ℝ → ℝ} (ha : Measurable a) {c : P × (ℝ × HeatCircle) → ℝ} (hc : Measurable c)
    (G : P → ℝ → State n → ℝ)
    (hH : Measurable (fun p : (P × ℝ) × State n => GaussianTaylor.hessian (G p.1.1 p.1.2) p.2)) :
    Measurable (fun p : (P × ℝ) × HeatCircle =>
      insertion a (fun q => c (p.1.1, q)) Z p.1.2 p.2 (G p.1.1 p.1.2)
        (observe (fun t => U (p.1.1, t)) (fun q => X (p.1.1, q)) (appendObservation Z p.1.2 p.2) p.1.2)) := by
  have hY := observe_joint_measurable Z hU hX
  have hHm : Measurable (fun p : (P × ℝ) × HeatCircle => GaussianTaylor.hessian (G p.1.1 p.1.2)
      (observe (fun t => U (p.1.1, t)) (fun q => X (p.1.1, q)) Z p.1.2)) :=
    hH.comp (measurable_fst.prodMk (hY.comp measurable_fst))
  have hrow : Measurable (fun p : (P × ℝ) × HeatCircle => heatRow Z p.1.2 p.2) :=
    (heatRow_joint_measurable Z).comp (measurable_fst.snd.prodMk measurable_snd)
  have heval₁ : Continuous (fun p : (State n →L[ℝ] State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have heval₂ : Continuous (fun p : (State n →L[ℝ] ℝ) × State n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hdir := heval₂.measurable.comp ((heval₁.measurable.comp (hHm.prodMk hrow)).prodMk hrow)
  have hmap : Measurable (fun p : (P × ℝ) × HeatCircle => (p.1.1, (p.1.2, p.2))) := by fun_prop
  have hcoef := (ha.comp (hX.comp hmap)).sub (hc.comp hmap)
  convert (hcoef.const_mul (1 / 2 : ℝ)).mul hdir using 1
  funext p
  rw [insertion_observe]
  rfl

end SHE.ObservationMeasurable
