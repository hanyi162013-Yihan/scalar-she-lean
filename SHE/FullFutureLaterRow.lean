module

public import SHE.FullFutureDampedHeat
public import SHE.PhysicalMeanEnergy
public import SHE.StopWeightedRows
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.FullFutureDampedHeat
open Set Filter MeasureTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement MeasurableGaussianScores PhysicalMeanEnergy FullFutureScoreOrder
open scoped BigOperators Topology
local instance fullFutureLaterRow_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

theorem row_continuous_lambda (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (q r : ℝ) (y : HeatCircle) : Continuous (fun Λ=>row σ target center q Λ r y) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n=>ℝ)).comp
  apply continuous_pi
  intro i
  change Continuous (fun Λ : ℝ=>exp (-Λ*(σ i-q))*
    (ProfileVariance.heatPhysical (target i-r) (center i) y).re)
  fun_prop

theorem weightedHeatRow_eq (Λ : ℝ) (Z : Fin n→WordRecursion.Observation)
    (q r : ℝ) (y : HeatCircle) :
    StopWeightedRows.weightedHeatRow Λ Z q r y=
      row (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q Λ r y := by
  apply PiLp.ext
  intro i
  rw [StopWeightedRows.weightedHeatRow,StopWeightedRows.diagonal_apply]
  rfl

/-- Zero damping is a genuine limit inside the fixed finite covariance
range. The same constant works for every nonnegative damping rate. -/
theorem damped_row_heat_bound_nonnegative (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i≤target i) → ∀ {u Λ δ ell M : ℝ},0≤Λ → 0<δ →
      (∀ i,u+δ≤σ i) → (∀ i,target i-u≤H) →
      ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        row σ target center u Λ u y∈
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c u)).range ∧
        scoreVariance (stoppedCovariance σ target center c u) (row σ target center u Λ u y)≤
          C/(ell*δ)*∑ i,‖ProfileVariance.heatPhysical (4*(target i-u)) (center i) y‖ := by
  obtain ⟨H,C,hH,hC,hV⟩ := damped_row_heat_bound n
  refine ⟨H,C,hH,hC,?_⟩
  intro σ target center hages u Λ δ ell M hΛ hδ hstop hsmall c hc hell hb
  by_cases hp : 0<Λ
  · exact hV σ target center hages hp hδ hstop hsmall c hc hell hb
  have hzero : Λ=0 := le_antisymm (le_of_not_gt hp) hΛ
  subst Λ
  let rate : ℕ→ℝ := fun j=>1/((j:ℝ)+1)
  have hrate (j : ℕ) : 0<rate j := by dsimp [rate];positivity
  have hlim : Tendsto rate atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hseq (j : ℕ) := hV σ target center hages (hrate j) hδ hstop hsmall c hc hell hb
  filter_upwards [ae_all_iff.mpr hseq] with y hy
  have hd := (row_continuous_lambda σ target center u u y).continuousAt.tendsto.comp hlim
  refine ⟨Submodule.closed_of_finiteDimensional _ |>.mem_of_tendsto hd
    (Eventually.of_forall (fun j=>(hy j).1)),?_⟩
  have he := (scoreVariance_continuous_direction (stoppedCovariance σ target center c u)).continuousAt.tendsto.comp hd
  exact le_of_tendsto he (Eventually.of_forall (fun j=>(hy j).2))

/-- The Gaussian/current law stays at q, and the heat row is genuinely
evaluated at r. Restoring the earlier covariance can only decrease its
canonical score energy. The stop weights remain anchored at q. -/
theorem later_row_heat_bound (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i≤target i) → ∀ {q r Λ δ ell M : ℝ},0≤q → q≤r → 0≤Λ → 0<δ →
      (∀ i,r+δ≤σ i) → (∀ i,target i-r≤H) →
      ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        row σ target center q Λ r y∈
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c q)).range ∧
        scoreVariance (stoppedCovariance σ target center c q) (row σ target center q Λ r y)≤
          exp (-Λ*(r-q))^2 * (C/(ell*δ)*
            ∑ i,‖ProfileVariance.heatPhysical (4*(target i-r)) (center i) y‖) := by
  obtain ⟨H,C,hH,hC,hV⟩ := damped_row_heat_bound_nonnegative n
  refine ⟨H,C,hH,hC,?_⟩
  intro σ target center hages q r Λ δ ell M hq hqr hΛ hδ hstop hsmall c hc hell hb
  have hcb (p : Domain) : 0≤c p ∧ c p≤M := ⟨hell.le.trans (hb p).1,(hb p).2⟩
  filter_upwards [hV σ target center hages hΛ hδ hstop hsmall c hc hell hb] with y hy
  have hR := range_mono_lower σ target center hages c hc hcb hq hqr hy.1
  rw [row_factor]
  refine ⟨Submodule.smul_mem _ _ hR,?_⟩
  rw [scoreVariance_smul]
  exact mul_le_mul_of_nonneg_left
    ((score_antitone_lower σ target center hages c hc hcb hq hqr hy.1).trans hy.2) (sq_nonneg _)

end SHE.FullFutureDampedHeat
