module

public import SHE.CovarianceFamilies
public import SHE.ObservationMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual Borel calculus for variable observation targets, centers and
stops. This includes every appended space-time node in a word history. -/
noncomputable section
namespace SHE.VariableObservations
open Set MeasureTheory ProbabilityTheory StoppedFourier ProfileVariance
open WordRecursion CovarianceMatrix CovarianceEndpoint GaussianContinuity
open scoped Matrix.Norms.Elementwise

abbrev State (n : ℕ) := WordRecursion.State n
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P]

structure Family (P : Type*) [MeasurableSpace P] (n : ℕ) where
  observations : P → Fin n → Observation
  stop_measurable : ∀ i, Measurable (fun p => (observations p i).stop)
  target_measurable : ∀ i, Measurable (fun p => (observations p i).target)
  center_measurable : ∀ i, Measurable (fun p => (observations p i).center)

theorem heatPhysical_joint_measurable :
    Measurable (fun p : ℝ × (HeatCircle × HeatCircle) => heatPhysical p.1 p.2.1 p.2.2) := by
  unfold heatPhysical heatCrossKernel
  apply Measurable.tsum
  intro n
  have he : Measurable (fun p : ℝ × (HeatCircle × HeatCircle) => (Real.exp (-p.1 * (n : ℝ)^2) : ℂ)) := by fun_prop
  exact (he.mul ((fourier n).continuous.measurable.comp measurable_snd.snd)).mul
    ((fourier (-n)).continuous.measurable.comp measurable_snd.fst)

namespace Family

def fixed {n : ℕ} (Z : Fin n → Observation) : Family P n where
  observations := fun _ => Z
  stop_measurable := fun _ => measurable_const
  target_measurable := fun _ => measurable_const
  center_measurable := fun _ => measurable_const

def append {n : ℕ} (Z : Family P n) : Family (P × (ℝ × HeatCircle)) (n + 1) where
  observations := fun p => appendObservation (Z.observations p.1) p.2.1 p.2.2
  stop_measurable := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_snd.fst
    · exact (Z.stop_measurable j).comp measurable_fst
  target_measurable := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_snd.fst
    · exact (Z.target_measurable j).comp measurable_fst
  center_measurable := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_snd.snd
    · exact (Z.center_measurable j).comp measurable_fst

theorem heatRow_entry_measurable {n : ℕ} (Z : Family P n) (i : Fin n) :
    Measurable (fun p : P × (ℝ × HeatCircle) => heatRow (Z.observations p.1) p.2.1 p.2.2 i) := by
  exact Complex.measurable_re.comp (heatPhysical_joint_measurable.comp
    ((((Z.target_measurable i).comp measurable_fst).sub measurable_snd.fst).prodMk
      (((Z.center_measurable i).comp measurable_fst).prodMk measurable_snd.snd)))

theorem heatRow_measurable {n : ℕ} (Z : Family P n) :
    Measurable (fun p : P × (ℝ × HeatCircle) => heatRow (Z.observations p.1) p.2.1 p.2.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact Measurable.of_eval Z.heatRow_entry_measurable

theorem observe_measurable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
    {n : ℕ} (Z : Family P n) {U : P × ℝ → CircleL2} (hU : Measurable U)
    {X : P × (ℝ × HeatCircle) → ℝ} (hX : Measurable X) :
    Measurable (fun p : P × ℝ => observe (fun t => U (p.1, t)) (fun q => X (p.1, q)) (Z.observations p.1) p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have htarget := (Z.target_measurable i).comp (measurable_fst : Measurable (fun p : P × ℝ => p.1))
  have hcenter := (Z.center_measurable i).comp (measurable_fst : Measurable (fun p : P × ℝ => p.1))
  have hmean := PhysicalProfile.physicalHeatMean_joint_measurable.comp
    (hU.prodMk ((htarget.sub measurable_snd).prodMk hcenter))
  have hstate := hX.comp (measurable_fst.prodMk (measurable_snd.prodMk hcenter))
  exact hmean.ite (measurableSet_lt measurable_snd htarget) hstate

theorem density_measurable {n : ℕ} (Z : Family P n) {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) (i j : Fin n) :
    Measurable (fun p : P × ℝ => covarianceDensity (fun q => c (p.1, q)) (Z.observations p.1) p.2 i j) := by
  have hmap : Measurable (fun p : (P × ℝ) × HeatCircle => (p.1.1, (p.1.2, p.2))) := by fun_prop
  have hm := (((hc.comp hmap).mul ((Z.heatRow_entry_measurable i).comp hmap)).mul
    ((Z.heatRow_entry_measurable j).comp hmap)).stronglyMeasurable.integral_prod_right'
      (ν := AddCircle.haarAddCircle)
  exact hm.measurable

theorem covariance_measurable {n : ℕ} (Z : Family P n) {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) {q s : P → ℝ} (hq : Measurable q) (hs : Measurable s)
    (hqs : ∀ p, q p ≤ s p) :
    Measurable (fun p => covariance (fun r => c (p, r)) (Z.observations p) (q p) (s p)) := by
  classical
  apply Measurable.of_eval_matrix
  intro i j
  have hD := Z.density_measurable hc i j
  have hset : MeasurableSet {p : P × ℝ | q p.1 < p.2 ∧ p.2 ≤ s p.1} :=
    (measurableSet_lt (hq.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hs.comp measurable_fst))
  have hm : Measurable (fun p : P × ℝ => if q p.1 < p.2 ∧ p.2 ≤ s p.1 then
      covarianceDensity (fun r => c (p.1, r)) (Z.observations p.1) p.2 i j else 0) :=
    hD.ite hset (measurable_const (a := (0 : ℝ)))
  have hi := hm.stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hi.measurable using 1
  funext p
  change (∫ t in q p..s p, covarianceDensity (fun r => c (p, r)) (Z.observations p) t i j) = _
  rw [intervalIntegral.integral_of_le (hqs p), ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Set.indicator, mem_Ioc]

theorem positive_covariance_measurable {n : ℕ} (Z : Family P n) {c : P × (ℝ × HeatCircle) → ℝ}
    (hc : Measurable c) {q s : P → ℝ} (hq : Measurable q) (hs : Measurable s)
    (hqs : ∀ p, q p ≤ s p)
    (hpos : ∀ p, (covariance (fun r => c (p, r)) (Z.observations p) (q p) (s p)).PosSemidef) :
    Measurable (fun p => (⟨covariance (fun r => c (p, r)) (Z.observations p) (q p) (s p), hpos p⟩ : PositiveCovariance n)) :=
  (Z.covariance_measurable hc hq hs hqs).subtype_mk

end Family
end SHE.VariableObservations
