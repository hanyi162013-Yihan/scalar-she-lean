module

public import SHE.UniformFutureDecayScores
public import SHE.ControlledOldIntervals
public import SHE.ControlledFixedReserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.AllDataDecayFreshScore
open Set Filter MeasureTheory AddCircle Real StoppedFourier StoppedGaussianFeatures ControlledOldIntervals
  GaussianIncrement MeasurableGaussianScores WordRecursion StopWeightedRows
open scoped BigOperators
local instance allDataDecayFreshScore_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {ι : Type*} {n k : ℕ}

/-- The true controlled full-residual first-score event is shared by
ALL initial states and ALL interpolation parameters simultaneously.
Thus actual past-dependent data can be substituted on this same event.
Every old interval and original stopped/target row remains literal. -/
theorem all_data_decay_ae (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (u d : ι→CircleL2) (lo upper : Fin k→ℝ)
    (hdisjoint : ∀ j l,j≠l→upper j ≤ lo l ∨ upper l ≤ lo j)
    (Z : Fin n→Observation) (hages : ∀ i,(Z i).stop ≤ (Z i).target)
    {q r hi : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hrhi : r<hi)
    (hstop : ∀ i,hi ≤ (Z i).stop)
    (hsmall : ∀ i,(Z i).target-r ≤ UniformFutureProfileScores.horizon n) :
    ∀ᵐ y : HeatCircle ∂haarAddCircle,∀ a θ,
      weightedHeatRow Λ Z q r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
        (ControlledFixedReserve.covariance P Λ (u a) (d a) (fixedProfile P Λ (u a) (d a) lo upper)
          (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q θ)).range ∧
      sqrt (scoreVariance (ControlledFixedReserve.covariance P Λ (u a) (d a)
          (fixedProfile P Λ (u a) (d a) lo upper)
          (fun i=>(Z i).stop) (fun i=>(Z i).target) (fun i=>(Z i).center) q θ)
        (weightedHeatRow Λ Z q r y)) ≤ 
        exp (-Λ*(r-q))*sqrt (2*UniformFutureProfileScores.constant n/(P.lower*(hi-r)))*
          ∑ i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖ := by
  let c : (ι×ℝ)→Domain→ℝ := fun a=>ControlledFixedReserve.coefficient P Λ (u a.1) (d a.1)
    (fixedProfile P Λ (u a.1) (d a.1) lo upper) a.2
  have hc (a : ι×ℝ) : Measurable (c a) :=
    ((ControlledProfile.profile_measurable P Λ (u a.1) (d a.1)).comp
      (measurable_const.prodMk measurable_id)).sub (fixedProfile_measurable P Λ (u a.1) (d a.1) lo upper)
  have hb (a : ι×ℝ) (p : Domain) : P.lower/2 ≤ c a p ∧ c a p ≤ P.upper :=
    residual_bounds P Λ (u a.1) (d a.1) lo upper hdisjoint a.2 p
  filter_upwards [UniformFutureProfileScores.weighted_decay_all_profiles_ae Z hages hq hqr hrhi hΛ hstop hsmall
    c hc (half_pos P.lower_pos) hb] with y hy
  intro a θ
  have hh := hy (a,θ)
  have hcoef : UniformFutureProfileScores.constant n/((P.lower/2)*(hi-r))=
      2*UniformFutureProfileScores.constant n/(P.lower*(hi-r)) := by
    field_simp [P.lower_pos.ne',(sub_pos.mpr hrhi).ne']
    <;> ring
  simpa only [c,ControlledFixedReserve.covariance,hcoef] using hh

end SHE.AllDataDecayFreshScore
