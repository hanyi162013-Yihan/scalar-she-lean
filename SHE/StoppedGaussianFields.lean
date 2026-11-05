module

public import SHE.MeasurableGaussianScores
public import SHE.StoppedGaussianFeatures
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

/-! Jointly Borel Gaussian scores for the genuine individually stopped
history covariance. The lower cutoff, stops, targets, centers, coefficient
profile, and observation direction may all vary measurably. -/
namespace SHE.StoppedGaussianFields
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier
  StoppedGaussianFeatures MeasurableGaussianScores GaussianIncrement
open scoped InnerProductSpace
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {P : Type*} [MeasurableSpace P] {n : ℕ}

def row (Z : VariableObservations.Family P n) (p : P) (r : Domain) : State n :=
  stoppedRow (fun i => (Z.observations p i).stop)
    (fun i => (Z.observations p i).target) (fun i => (Z.observations p i).center) r

theorem row_entry_measurable (Z : VariableObservations.Family P n) (i : Fin n) :
    Measurable (fun p : P × Domain => row Z p.1 p.2 i) := by
  have hset : MeasurableSet {p : P × Domain | p.2.1 < (Z.observations p.1 i).stop} :=
    measurableSet_lt measurable_snd.fst ((Z.stop_measurable i).comp measurable_fst)
  exact (Z.heatRow_entry_measurable i).ite hset measurable_const

theorem row_measurable (Z : VariableObservations.Family P n) :
    Measurable (fun p : P × Domain => row Z p.1 p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  exact Measurable.of_eval (row_entry_measurable Z)

def covariance (Z : VariableObservations.Family P n) (c : P × Domain → ℝ)
    (q : P → ℝ) (p : P) : Matrix (Fin n) (Fin n) ℝ :=
  StoppedGaussianFeatures.stoppedCovariance (fun i => (Z.observations p i).stop)
    (fun i => (Z.observations p i).target) (fun i => (Z.observations p i).center)
    (fun r => c (p, r)) (q p)

theorem covariance_global_integral (Z : VariableObservations.Family P n)
    (c : P × Domain → ℝ) (q : P → ℝ) (p : P) (i j : Fin n) :
    covariance Z c q p i j =
      ∫ r : Domain, (if q p ≤ r.1 then c (p, r) * row Z p r i * row Z p r j else 0)
        ∂volume.prod (haarAddCircle (T := 2 * Real.pi)) := by
  unfold covariance StoppedGaussianFeatures.stoppedCovariance historyMeasure
  rw [Measure.restrict_prod_eq_prod_univ, ← integral_indicator
    (measurableSet_Ici.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards with r
  simp only [Set.indicator, mem_prod, mem_Ici, mem_univ, and_true, row]

/-- Actual Borel dependence of the full individually stopped covariance,
including varying lower cutoff and arbitrary rank changes. -/
theorem covariance_measurable (Z : VariableObservations.Family P n)
    {c : P × Domain → ℝ} (hc : Measurable c) {q : P → ℝ} (hq : Measurable q) :
    Measurable (covariance Z c q) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hset : MeasurableSet {p : P × Domain | q p.1 ≤ p.2.1} :=
    measurableSet_le (hq.comp measurable_fst) measurable_snd.fst
  have hm : Measurable (fun p : P × Domain => if q p.1 ≤ p.2.1 then
      c p * row Z p.1 p.2 i * row Z p.1 p.2 j else 0) :=
    ((hc.mul (row_entry_measurable Z i)).mul (row_entry_measurable Z j)).ite hset measurable_const
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.prod (haarAddCircle (T := 2 * Real.pi)))
  convert! hi.measurable using 1
  funext p
  exact covariance_global_integral Z c q p i j

theorem covariance_posSemidef (Z : VariableObservations.Family P n)
    (c : P × Domain → ℝ) (q : P → ℝ) (p : P)
    (hc : Measurable (fun r => c (p, r))) {M : ℝ}
    (hcb : ∀ r, 0 ≤ c (p, r) ∧ c (p, r) ≤ M)
    (hages : ∀ i, (Z.observations p i).stop ≤ (Z.observations p i).target) :
    (covariance Z c q p).PosSemidef := by
  rw [covariance, ← weightedFeature_gram _ _ _ _ hc M hcb hages]
  exact Matrix.posSemidef_gram ℝ _

def dampedDirection (Z : VariableObservations.Family P n) (u Λ : P → ℝ)
    (p : P) (x : HeatCircle) : State n :=
  WithLp.toLp 2 (fun i => Real.exp (-Λ p * ((Z.observations p i).stop - u p)) *
    row Z p (u p, x) i)

def defectDirection (Z : VariableObservations.Family P n) (u Λ : P → ℝ)
    (p : P) (x : HeatCircle) : State n :=
  WithLp.toLp 2 (fun i => (1 - Real.exp (-Λ p * ((Z.observations p i).stop - u p))) *
    row Z p (u p, x) i)

theorem dampedDirection_measurable (Z : VariableObservations.Family P n)
    {u Λ : P → ℝ} (hu : Measurable u) (hΛ : Measurable Λ) :
    Measurable (fun p : P × HeatCircle => dampedDirection Z u Λ p.1 p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hr := (row_entry_measurable Z i).comp
    (measurable_fst.prodMk ((hu.comp measurable_fst).prodMk measurable_snd))
  exact (((hΛ.comp measurable_fst).neg.mul
    (((Z.stop_measurable i).comp measurable_fst).sub (hu.comp measurable_fst))).exp).mul hr

theorem defectDirection_measurable (Z : VariableObservations.Family P n)
    {u Λ : P → ℝ} (hu : Measurable u) (hΛ : Measurable Λ) :
    Measurable (fun p : P × HeatCircle => defectDirection Z u Λ p.1 p.2) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hr := (row_entry_measurable Z i).comp
    (measurable_fst.prodMk ((hu.comp measurable_fst).prodMk measurable_snd))
  exact (measurable_const.sub (((hΛ.comp measurable_fst).neg.mul
    (((Z.stop_measurable i).comp measurable_fst).sub (hu.comp measurable_fst))).exp)).mul hr

/-- These are literal Borel score functions; no parameterwise nonmeasurable
choice of a Gaussian direction is needed. -/
theorem firstScore_field_measurable (Z : VariableObservations.Family P n)
    {c : P × Domain → ℝ} (hc : Measurable c) {q : P → ℝ} (hq : Measurable q)
    {d : P → State n} (hd : Measurable d) :
    Measurable (fun p : P × State n => firstScore (covariance Z c q p.1) (d p.1) p.2) := by
  convert! firstScore_measurable.comp
    ((((covariance_measurable Z hc hq).prodMk hd).comp measurable_fst).prodMk measurable_snd) using 1

theorem secondScore_field_measurable (Z : VariableObservations.Family P n)
    {c : P × Domain → ℝ} (hc : Measurable c) {q : P → ℝ} (hq : Measurable q)
    {d : P → State n} (hd : Measurable d) :
    Measurable (fun p : P × State n => secondScore (covariance Z c q p.1) (d p.1) p.2) := by
  convert! secondScore_measurable.comp
    ((((covariance_measurable Z hc hq).prodMk hd).comp measurable_fst).prodMk measurable_snd) using 1

end SHE.StoppedGaussianFields
