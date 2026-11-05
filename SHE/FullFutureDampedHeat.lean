module

public import SHE.FullFutureScoreOrder
public import SHE.NativeHeatKernel
public import SHE.NativeHeatDilation
public import SHE.GaussianScoreQuadratic
public import SHE.PhysicalTerminalHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section

namespace SHE.FullFutureDampedHeat
open Set MeasureTheory Real AddCircle StoppedFourier StoppedGaussianFeatures GaussianIncrement
  MeasurableGaussianScores StoppedCanonicalScore NativeHeatSpan
open scoped BigOperators
local instance fullFutureDampedHeat_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {n : ℕ}

/-- Original stop-damping is anchored at Gaussian/current time q,
while the physical heat row may be evaluated at a later time r. -/
def row (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (q Λ r : ℝ) (y : HeatCircle) : State n :=
  WithLp.toLp 2 (fun i=>exp (-Λ*(σ i-q))*(ProfileVariance.heatPhysical (target i-r) (center i) y).re)

theorem row_factor (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (q Λ r : ℝ) (y : HeatCircle) :
    row σ target center q Λ r y=exp (-Λ*(r-q)) • row σ target center r Λ r y := by
  apply PiLp.ext
  intro i
  change exp (-Λ*(σ i-q))*_=exp (-Λ*(r-q))*(exp (-Λ*(σ i-r))*_)
  rw [←mul_assoc,←exp_add]
  congr 2
  ring

/-- Literal native Haar/heat-kernel form of the full stopped-history
damped score. Stops, targets and centers are unrestricted apart from
their actual positive observation gap. -/
theorem damped_row_heat_bound (n : ℕ) :
    ∃ H C : ℝ,0<H ∧ 0<C ∧
      ∀ (σ target : Fin n→ℝ) (center : Fin n→HeatCircle),
      (∀ i,σ i≤target i) → ∀ {u Λ δ ell M : ℝ},0<Λ → 0<δ →
      (∀ i,u+δ≤σ i) → (∀ i,target i-u≤H) →
      ∀ (c : Domain→ℝ),Measurable c → 0<ell → (∀ p,ell≤c p ∧ c p≤M) →
      ∀ᵐ y : HeatCircle ∂haarAddCircle,
        row σ target center u Λ u y∈
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (stoppedCovariance σ target center c u)).range ∧
        scoreVariance (stoppedCovariance σ target center c u) (row σ target center u Λ u y)≤
          C/(ell*δ)*∑ i,‖ProfileVariance.heatPhysical (4*(target i-u)) (center i) y‖ := by
  obtain ⟨h,K,hh,hh1,hK,hscore⟩ := stopped_damped_score_bound n
  refine ⟨4*π^2*h,2*K*sqrt (8*π)*sqrt 2,by positivity,by positivity,?_⟩
  intro σ target center hages u Λ δ ell M hΛ hδ hstop hsmall c hc hell hb
  let a : Fin n→UnitAddCircle := fun i=>unitCenter (center i)
  let t : Fin n→ℝ := fun i=>clock (target i-u)
  have hage (i : Fin n) : 0<target i-u := by linarith [hstop i,hages i]
  have ht (i : Fin n) : 0<t i := clock_pos (hage i)
  have hth (i : Fin n) : t i≤h := by
    exact (div_le_iff₀ (by positivity : 0<4*π^2)).mpr (by simpa only [mul_comm] using hsmall i)
  have he (i : Fin n) : target i-u=4*π^2*t i := by dsimp [t,clock];field_simp
  have hcb (p : Domain) : 0≤c p ∧ c p≤M := ⟨hell.le.trans (hb p).1,(hb p).2⟩
  have hsc := hscore σ target a u Λ hΛ t ht hth he hages δ hδ hstop c hc M ell hcb hell (fun p=>(hb p).1)
  have hnat := (CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae hsc
  have hweights (i : Fin n) := weight_le_physical_ae (hage i) (center i)
  filter_upwards [hnat,ae_all_iff.mpr hweights] with y hy hw
  have hcenter : StoppedGaussianScore.nativeCenter a=center := by
    funext i
    exact scale_inverse (center i)
  have hrow : physicalDampedDirection σ target a u Λ (unitCenter y)=row σ target center u Λ u y := by
    apply PiLp.ext
    intro i
    change exp (-Λ*(σ i-u))*(ProfileVariance.heatPhysical (target i-u)
      (StoppedGaussianScore.nativeCenter a i) (CircleNormalization.scale 1 (2*π) (unitCenter y))).re=_
    rw [hcenter,scale_inverse]
    rfl
  dsimp only [unitCenter] at hrow
  simp only [hcenter,hrow] at hy
  refine ⟨hy.1,hy.2.trans ?_⟩
  have hsum : (∑ i,GlobalTorusHeatSpan.weight (t i) (a i) (unitCenter y))≤
      sqrt (8*π)*sqrt 2*∑ i,‖ProfileVariance.heatPhysical (4*(target i-u)) (center i) y‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := (hw i).trans (mul_le_mul_of_nonneg_left
      (NativeHeatSpan.physical_two_le_four (hage i) (center i) y) (sqrt_nonneg (8*π)))
    simpa only [t,a,NativeHeatSpan.weight,mul_assoc] using hi
  have hs := mul_le_mul_of_nonneg_left hsum (div_nonneg (by positivity : 0≤2*K) (mul_nonneg hell.le hδ.le))
  convert! hs using 1 <;> ring

end SHE.FullFutureDampedHeat
