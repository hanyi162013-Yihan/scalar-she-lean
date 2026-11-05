module

public import SHE.PointScoreDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalParentGeometry
open StoppedFourier CutoffWordHistories
variable {P : Type} [MeasurableSpace P]
theorem replaceSpace_self (k : ℕ) (p : History P k) :
    replaceSpace k p (PhysicalChainArrays.space k p)=p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (replaceSpace k p.1 (fun i => PhysicalChainArrays.space (k+1) p i.succ),p.2.1,
      PhysicalChainArrays.space (k+1) p 0)=p
    simpa only [PhysicalChainArrays.space,Fin.cases_zero,Fin.cases_succ,ih p.1] using Prod.eta p
end SHE.PhysicalParentGeometry

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays CoveredTerminalMoments
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

/-- The same nonnegative density written directly on the actual history,
so its moment inequality is a genuine jointly Borel event before Fubini. -/
def globalDensity (c : StoppedGaussianFeatures.Domain → ℝ) (k : ℕ) (p : History P k)
    (q : ℝ) (y : HeatCircle) : ℝ :=
  max (scoreProduct L ((carrier L k).observations.observations p) c k p) 0*
    ∑ i : Fin (1+k),Real.sqrt ‖ProfileVariance.heatPhysical
      (4*(((carrier L k).observations.observations p i).target-q))
      ((carrier L k).observations.observations p i).center y‖

theorem globalDensity_replaceSpace (c : StoppedGaussianFeatures.Domain → ℝ) (k : ℕ)
    (p : History P k) (q : ℝ) (y : HeatCircle) (x : Fin k → HeatCircle) :
    globalDensity L c k (replaceSpace k p x) q y=density L c k p q y x := by
  unfold globalDensity density spatialScore
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [terminalHeat,congrFun (replaceSpace_targets L k p x) i]

theorem globalDensity_measurable (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    (k : ℕ) (q : ℝ) : Measurable (fun z : History P k × HeatCircle => globalDensity L c k z.1 q z.2) := by
  unfold globalDensity
  apply (((scoreProduct_measurable L c hc k).comp measurable_fst).max measurable_const).mul
  apply Finset.measurable_sum
  intro i _
  have hT := ((carrier L k).observations.target_measurable i).comp
    (measurable_fst : Measurable (Prod.fst : History P k × HeatCircle → History P k))
  have hx := ((carrier L k).observations.center_measurable i).comp
    (measurable_fst : Measurable (Prod.fst : History P k × HeatCircle → History P k))
  exact Real.continuous_sqrt.measurable.comp
    (ProfileVariance.heatPhysical_joint_measurable.comp
      ((((hT.sub_const q).const_mul 4).prodMk hx).prodMk measurable_snd)).norm

/-- Absolute score-scale envelope on the actual full history, with
singular old-score nonnegativity stated where its actual AE proof applies. -/
theorem global_score_density (k : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (c : StoppedGaussianFeatures.Domain → ℝ), Measurable c →
    ∀ {ell M : ℝ}, 0 < ell → (∀ r,ell ≤ c r ∧ c r ≤ M) →
    ∀ (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target),
    ∀ (p : History P k) {q : ℝ}, 0 ≤ q → q < (carrier L k).terminal p →
    (∀ i,((carrier L k).observations.observations p i).target-q ≤ H) →
    0 ≤ scoreProduct L ((carrier L k).observations.observations p) c k p →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      |scoreScale L c k p q (heatRow ((carrier L k).observations.observations p) q y)| ≤
        Real.sqrt (C/(ell*((carrier L k).terminal p-q)))*globalDensity L c k p q y := by
  obtain ⟨H,C,hH,hC,hV⟩ := point_score_density L k
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell M hell hb hages p q hq0 hq hsmall hn
  have hn' : 0 ≤ spatialScore L c k p (space k p) := by
    simpa only [spatialScore,replaceSpace_self] using hn
  have hh := hV c hc hell hb hages p hq0 hq hsmall (space k p) hn'
  filter_upwards [hh] with y hy
  have hpos : 0 ≤ scoreScale L c k p q (heatRow ((carrier L k).observations.observations p) q y) :=
    mul_nonneg (Real.sqrt_nonneg _) hn
  rw [abs_of_nonneg hpos]
  simpa only [replaceSpace_self,←globalDensity_replaceSpace] using hy

end SHE.ScalarMeanEnvelope
