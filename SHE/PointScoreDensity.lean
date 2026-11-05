module

public import SHE.PhysicalTerminalHeat
public import SHE.ScalarMeanEnvelope
public import SHE.CoveredTerminalMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays CoveredTerminalMoments
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

/-- The exact terminal-first/old-second score scale is bounded by the
nonnegative scalar spatial density. The fresh interval contributes only
a square-root inverse gap. Parent centers are fixed before this AE input
point estimate is applied. -/
theorem point_score_density (k : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
    ∀ (c : StoppedGaussianFeatures.Domain → ℝ), Measurable c →
    ∀ {ell M : ℝ}, 0 < ell → (∀ r,ell ≤ c r ∧ c r ≤ M) →
    ∀ (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target),
    ∀ (p : History P k) {q : ℝ}, 0 ≤ q → q < (carrier L k).terminal p →
    (∀ i,((carrier L k).observations.observations p i).target-q ≤ H) →
    ∀ (x : Fin k → HeatCircle), 0 ≤ spatialScore L c k p x →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      scoreScale L c k (replaceSpace k p x) q
        (heatRow ((carrier L k).observations.observations (replaceSpace k p x)) q y) ≤
          Real.sqrt (C/(ell*((carrier L k).terminal p-q)))*density L c k p q y x := by
  obtain ⟨H,C,hH,hC,hV⟩ := PhysicalFirstScore.terminal_sqrt_heat_envelope (1+k)
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell M hell hb hages p q hq0 hq hsmall x hn
  let Z := (carrier L k).observations.observations (replaceSpace k p x)
  have hgap : q < (carrier L k).terminal (replaceSpace k p x) := by
    simpa only [replaceSpace_terminal] using hq
  have htarget := replaceSpace_targets L k p x
  have hsmall' (i) : (Z i).target-q ≤ H := by
    simpa only [Z,←congrFun htarget i] using hsmall i
  have hv := hV Z (RecursiveScoreSupport.carrier_ages L hages k (replaceSpace k p x))
    hq0 hgap ((carrier L k).stops_after (replaceSpace k p x)) hsmall' c hc hell hb
  filter_upwards [hv] with y hy
  have hh := mul_le_mul_of_nonneg_right hy hn
  have hE : (∑ i : Fin (1+k),Real.sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-q)) (Z i).center y‖)=
      ∑ i : Fin (1+k),Real.sqrt (terminalHeat L k p q y i x) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [terminalHeat,Z,congrFun htarget i]
  have hpref : Real.sqrt (C/(ell*((carrier L k).terminal (replaceSpace k p x)-q)))=
      Real.sqrt (C/(ell*((carrier L k).terminal p-q))) := by rw [replaceSpace_terminal]
  rw [hE,hpref] at hh
  simp only [density,max_eq_left hn]
  simpa only [scoreScale,spatialScore,scoreProduct,mul_assoc,mul_comm,mul_left_comm,Z] using hh

end SHE.ScalarMeanEnvelope
