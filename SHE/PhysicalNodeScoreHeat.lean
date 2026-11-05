module

public import SHE.PhysicalScoreFrame
public import SHE.IntervalScoreHeatKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianCoordinates FixedOldScoreSupport OldIntervalCovariance
  MeasurableGaussianScores ScoreProjectionEnergy StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The old-score envelope is first proved in the actual earlier frame.
Its centers depend only on the older history, never on the newly integrated
location. This is the correct spatial AE applicability for growing words. -/
theorem node_score_heat (k : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (c : Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    (∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target) →
    ∀ (p : History P k) (t : ℝ), R.base < t → t < (carrier L k).terminal p →
    (∀ i, ((carrier L k).observations.observations p i).target-t ≤ H) →
    ∀ᵐ x : HeatCircle ∂AddCircle.haarAddCircle,
      scoreVariance (profileCovariances L c k (p,t,x)) (row L k (p,t,x)) ≤
        (C/(ell*((carrier L k).terminal p-t)))*
          ∑ i : Fin (n+k), ‖ProfileVariance.heatPhysical
            (2*(((carrier L k).observations.observations p i).target-t))
            ((carrier L k).observations.observations p i).center x‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := IntervalScoreEnvelope.score_heat_kernel (n+k)
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages p t hbase hgap hsmall
  let Z := (carrier L k).observations.observations p
  let σ : Fin (n+k) → ℝ := fun i => (Z i).stop
  let target : Fin (n+k) → ℝ := fun i => (Z i).target
  let center : Fin (n+k) → HeatCircle := fun i => (Z i).center
  have hcb (r : Domain) : ell ≤ c r ∧ c r ≤ R.upper :=
    ⟨(hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
  have hnode (x : HeatCircle) : (carrier L k).nodeTime (p,t,x)=t :=
    ClippedCovariance.clip_eq ⟨hbase.le,hgap.le⟩
  have hcov : intervalCovariance Z c t ((carrier L k).terminal p)=
      WordRecursion.covariance c Z t ((carrier L k).terminal p) :=
    PhysicalIntervalCovariance.interval_eq_covariance Z c hc
      (fun r => by rw [abs_of_nonneg (hell.le.trans (hcb r).1)]; exact (hcb r).2)
      (RecursiveScoreSupport.carrier_ages L hages k p) ((carrier L k).stops_after p)
      (R.base_nonneg.trans hbase.le) hgap.le
  have hcovx (x : HeatCircle) : profileCovariances L c k (p,t,x)=
      intervalCovariance Z c t ((carrier L k).terminal p) := by
    unfold profileCovariances
    rw [hnode]
    exact hcov.symm
  have hrow (x : HeatCircle) : row L k (p,t,x)=stoppedRow σ target center (t,x) := by
    simp only [row,Interior,hbase,hgap,and_self,ite_true,hnode]
    ext i
    change (ProfileVariance.heatPhysical ((Z i).target-t) (Z i).center x).re =
      if t < (Z i).stop then (ProfileVariance.heatPhysical ((Z i).target-t) (Z i).center x).re else 0
    rw [ite_eq_left (hgap.trans_le ((carrier L k).stops_after p i))]
  have hactive : IntervalHistoryEnergy.active σ ((carrier L k).terminal p)=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    exact (carrier L k).stops_after p i
  have hh := hV σ target center (RecursiveScoreSupport.carrier_ages L hages k p)
    (R.base_nonneg.trans hbase.le) hgap (fun i => Or.inr ((carrier L k).stops_after p i))
    (fun i _ => hsmall i) c hc hell hcb
  filter_upwards [hh] with x hx
  rw [hcovx,hrow]
  simpa only [hactive,PhysicalScoreChain.intervalCovariance,σ,target,center,Z] using hx

end SHE.PhysicalScoreChain
