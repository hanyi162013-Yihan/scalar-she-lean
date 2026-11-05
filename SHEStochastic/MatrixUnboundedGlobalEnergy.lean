module

public import SHEStochastic.MatrixUnboundedGlobalWeakExistence
public import SHEStochastic.FiniteBlockEnergyMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixUnboundedGlobalEnergy
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable {G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {C β : ℝ≥0}
    {hG : HolderWith C β G} {hβ : 0<β} {hβ1 : β<1}
    {ρ₀ : MatrixLocalBlockChain.L2Law (n := n)}
    (S : MatrixUnboundedGlobalWeakExistence.Solution G hG hβ hβ1 ρ₀)

def sqState (p : ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1) : ℝ :=
  ‖MatrixGlobalBlockPath.state 1 p.1 p.2‖^2

theorem sqState_measurable : Measurable (sqState (n := n)) := by
  exact ((MatrixGlobalBlockPath.measurable 1).norm).pow_const 2

private theorem block_integrable (k : ℕ) :
    Integrable (fun p : ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1 =>
      sqState (n := n) ((k : ℝ≥0)+p.1,p.2))
      (energyMeasure S.law.toMeasure 1) := by
  apply (S.energy k).congr
  have htime : ∀ᵐ p ∂energyMeasure S.law.toMeasure 1, p.1 ≤ (1 : ℝ≥0) := by
    have hm : MeasurableSet {p : ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1 |
      p.1 ≤ (1 : ℝ≥0)} := measurableSet_le measurable_fst measurable_const
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [timeMeasure_ae_mem (1 : ℝ≥0)] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht.2)
  filter_upwards [htime] with p hp
  change ‖MatrixGlobalBlockFourier.state zero_lt_one k p‖^2 =
    ‖MatrixGlobalBlockPath.state 1 ((k : ℝ≥0)+p.1) p.2‖^2
  simpa only [mul_one] using
    congrArg (fun z => ‖z‖^2) (MatrixGlobalBlockFourier.state_eq zero_lt_one k p.1 hp p.2)

/-- The pasted unbounded vector state has finite expected square energy
on every finite integer horizon, using only the checked block energies. -/
theorem nat_energy (k : ℕ) :
    Integrable (sqState (n := n)) (energyMeasure S.law.toMeasure (k : ℝ≥0)) := by
  induction k with
  | zero =>
      have hz : energyMeasure S.law.toMeasure (0 : ℝ≥0) = 0 := by
        have ht : PredictableL2.timeMeasure (0 : ℝ≥0) = 0 :=
          (Measure.measure_univ_eq_zero).mp (by simpa using timeMeasure_mass (0 : ℝ≥0))
        simp [energyMeasure,ht]
      simpa only [Nat.cast_zero,hz] using (integrable_zero_measure :
        Integrable (sqState (n := n)) (0 : Measure (ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1)))
  | succ k ih =>
      rw [FiniteBlockEnergyMeasure.succ S.law.toMeasure k, integrable_add_measure]
      refine ⟨ih,?_⟩
      have hm : AEStronglyMeasurable (sqState (n := n))
          ((energyMeasure S.law.toMeasure ((k+1 : ℕ) : ℝ≥0)).restrict
            (Set.Ioc (k : ℝ≥0) ((k+1 : ℕ) : ℝ≥0) ×ˢ Set.univ)) :=
        (sqState_measurable (n := n)).stronglyMeasurable.aestronglyMeasurable
      have hp := DeterministicItoShift.product_translation S.law.toMeasure
        ((k+1 : ℕ) : ℝ≥0) (k : ℝ≥0) 1
        (by simp : (k : ℝ≥0)+1 ≤ ((k+1 : ℕ) : ℝ≥0))
      have hp' : MeasurePreserving
          (fun p : ℝ≥0 × MatrixGlobalBlockPath.Space (n := n) 1 =>
            ((k : ℝ≥0)+p.1,p.2))
          (energyMeasure S.law.toMeasure 1)
          ((energyMeasure S.law.toMeasure ((k+1 : ℕ) : ℝ≥0)).restrict
            (Set.Ioc (k : ℝ≥0) ((k+1 : ℕ) : ℝ≥0) ×ˢ Set.univ)) := by
        simpa only [Nat.cast_add,Nat.cast_one] using hp
      exact (hp'.integrable_comp hm).mp (block_integrable S k)

/-- Every finite physical horizon has enough state energy to define the
original unbounded predictable Fourier input on that horizon. -/
theorem finite_energy (T : ℝ≥0) :
    Integrable (sqState (n := n)) (energyMeasure S.law.toMeasure T) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (T : ℝ)
  have hTk : T ≤ (k : ℝ≥0) := by exact_mod_cast hk.le
  have ht : PredictableL2.timeMeasure T ≤ PredictableL2.timeMeasure (k : ℝ≥0) := by
    rw [← timeMeasure_restrict hTk]
    exact Measure.restrict_le_self
  have hp : energyMeasure S.law.toMeasure T ≤
      energyMeasure S.law.toMeasure (k : ℝ≥0) :=
    Measure.prod_mono ht le_rfl
  exact (nat_energy S k).mono_measure hp

end SHEStochastic.MatrixUnboundedGlobalEnergy
