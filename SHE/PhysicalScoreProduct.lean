module

public import SHE.PhysicalAllScoreBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
  PhysicalParentGeometry OrderedHeatForests
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def SmallHistory (H : ℕ → ℝ) : (k : ℕ) → History P k → Prop
  | 0,_ => True
  | k+1,p => SmallHistory H k p.1 ∧
      ∀ i, ((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p ≤ H k

def timeWeight (ell : ℝ) (C : ℕ → ℝ) : (k : ℕ) → History P k → ℝ
  | 0,_ => 1
  | k+1,p => timeWeight ell C k p.1 *
      (C k/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p)))

def scoreProduct (Z : Fin N → Observation) (c : Domain → ℝ) (k : ℕ) (p : History P k) : ℝ :=
  ∏ j : Fin k, scoreVariance (PhysicalChainArrays.covariances L Z c k p j)
    (PhysicalChainArrays.directions L Z k p j)

theorem scoreProduct_step (Z : Fin N → Observation) (c : Domain → ℝ) (k : ℕ)
    (p : History P (k+1)) :
    scoreProduct L Z c (k+1) p = scoreProduct L Z c k p.1 *
      scoreVariance (intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1))
        (direction L Z k p) := by
  unfold scoreProduct
  rw [Fin.prod_univ_succ]
  simp only [PhysicalChainArrays.covariances,PhysicalChainArrays.lower,PhysicalChainArrays.upper,
    PhysicalChainArrays.directions,Fin.cases_zero,Fin.cases_succ]
  exact mul_comm _ _

theorem timeWeight_nonneg {ell : ℝ} (hell : 0 < ell) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (k : ℕ) (p : History P k) (hp : StrictHistory L k p) : 0 ≤ timeWeight L ell C k p := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    have ht : (carrier L k).nodeTime p=p.2.1 := ClippedCovariance.clip_eq ⟨hp.2.1.le,hp.2.2.le⟩
    exact mul_nonneg (ih p.1 hp.1) (div_nonneg (hC k)
      (mul_nonneg hell.le (by rw [ht]; exact (sub_pos.mpr hp.2.2).le)))

theorem activeHeatProduct_nonneg (Z : Fin N → Observation) (k : ℕ) (p : History P k) :
    0 ≤ activeHeatProduct L Z k p :=
  Finset.prod_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- Actual full-frame old score energies have the true all-order parent
forest envelope. Local spatial exceptional sets have already been handled
in the earlier frame; no adaptive-center substitution is used. -/
theorem scoreProduct_heat_bound (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ r, ell ≤ c r ∧ c r ≤ R.reference r)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (H C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (hg : Function.Injective g)
    (hsel : Selection L Z k p g) (hp : StrictHistory L k p)
    (hsmall : SmallHistory L H k p) (hbound : AllNodeBounds L c ell H C k p)
    (hsup : RecursiveGaussianScores.Supported L (profileCovariances L c)
      (profileCovariances L (fun r => R.reference r-c r)) k p) :
    scoreProduct L Z c k p ≤ timeWeight L ell C k p*activeHeatProduct L Z k p := by
  induction k with
  | zero => simp only [scoreProduct,timeWeight,activeHeatProduct,Fin.prod_univ_zero,one_mul,le_refl]
  | succ k ih =>
    have hcb (r : Domain) : 0 ≤ c r ∧ c r ≤ R.upper :=
      ⟨hell.le.trans (hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
    have heq := node_scoreVariance_eq L c hc hcb hages Z hZ g hg hsel hsup.2.2.2.2
    have hnew : scoreVariance
        (intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1))
        (direction L Z k p) ≤
        (C k/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p)))*nodeHeat L k p := by
      rw [heq]
      exact hbound.2 hp.2 hsmall.2
    have hn : 0 ≤ scoreVariance
        (intervalCovariance Z c ((carrier L k).nodeTime p) ((carrier L k).terminal p.1))
        (direction L Z k p) := by
      rw [heq]
      exact scoreVariance_nonneg hsup.2.1 hsup.2.2.2.2
    have hprev := ih p.1 (fun i => g i.succ) (hg.comp (Fin.succ_injective _))
      hsel.tail hp.1 hsmall.1 hbound.1 hsup.1
    rw [scoreProduct_step]
    calc
      _ ≤ (timeWeight L ell C k p.1*activeHeatProduct L Z k p.1)*
          ((C k/(ell*((carrier L k).terminal p.1-(carrier L k).nodeTime p)))*nodeHeat L k p) :=
        mul_le_mul hprev hnew hn (mul_nonneg
          (timeWeight_nonneg L hell C hC k p.1 hp.1) (activeHeatProduct_nonneg L Z k p.1))
      _ = _ := by
        rw [activeHeatProduct_step,node_active_heat_sum L Z g hsel hg hp.2]
        dsimp only [timeWeight,nodeHeat]
        ring

end SHE.PhysicalScoreChain
