module

public import SHE.SeparatedRowScore
public import SHE.GlobalPointDensity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain PhysicalChainArrays CoveredTerminalMoments
open scoped BigOperators
local instance separatedGlobalDensityPeriod : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R X 1)

/-- The actual q-window score scale at row-time r is controlled by the
genuine r-age parent density. Earlier old Gaussian fractions and current
q-law remain unchanged, and the physical direction range is concluded. -/
theorem global_later_score_density (k : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
    ∀ (c : StoppedGaussianFeatures.Domain→ℝ),Measurable c →
    ∀ {ell M : ℝ},0<ell → (∀ p,ell≤c p ∧ c p≤M) →
    ∀ (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target),
    ∀ (p : History X k) {q r : ℝ},0≤q → q≤r → r<(carrier L k).terminal p →
    (carrier L k).terminal p≤1 →
    (∀ i,((carrier L k).observations.observations p i).target-r≤H) →
    0≤scoreProduct L ((carrier L k).observations.observations p) c k p →
    ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      heatRow ((carrier L k).observations.observations p) r y∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (intervalCovariance
          ((carrier L k).observations.observations p) c q ((carrier L k).terminal p))).range ∧
      |scoreScale L c k p q (heatRow ((carrier L k).observations.observations p) r y)|≤
        Real.sqrt (C/(ell*((carrier L k).terminal p-r)))*globalDensity L c k p r y := by
  obtain ⟨H,C,hH,hC,hV⟩ := PhysicalFirstScore.later_terminal_sqrt_heat_envelope (1+k)
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell M hell hb hages p q r hq hqr hr hhi hsmall hn
  have hh := hV ((carrier L k).observations.observations p)
    (RecursiveScoreSupport.carrier_ages L hages k p) hq hqr hr hhi
    ((carrier L k).stops_after p) hsmall c hc hell hb
  filter_upwards [hh] with y hy
  refine ⟨hy.1,?_⟩
  have hp : 0≤scoreScale L c k p q (heatRow ((carrier L k).observations.observations p) r y) :=
    mul_nonneg (Real.sqrt_nonneg _) hn
  rw [abs_of_nonneg hp]
  have hb' := mul_le_mul_of_nonneg_right hy.2 hn
  simp only [globalDensity,max_eq_left hn]
  simpa only [scoreScale,scoreProduct,mul_assoc,mul_comm,mul_left_comm] using hb'

end SHE.ScalarMeanEnvelope
