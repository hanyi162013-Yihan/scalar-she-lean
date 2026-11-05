module

public import SHE.NativeFirstScoreReserve
public import SHE.FullFutureWeightedScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.NativeReserveRowEnvelope
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion
  PhysicalScoreChain StoppedGaussianFeatures MeasurableGaussianScores StopWeightedRows
open scoped BigOperators
local instance nativeReserveRowEnvelope_period : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- The native reserve retains its OWN physical input-row score and
all original parent heat edges. The q-law remains fixed when the row
is evaluated later at r. Witnesses depend only on dimension. -/
theorem sqrt_heat_envelope (n:ℕ):
    ∃H C:ℝ,0<H ∧ 0<C ∧
      ∀(P:CanonicalCovariance.ProfileParameters) (Z:Fin n→Observation),
      (∀ i, (Z i).stop ≤ (Z i).target) → ∀ {q r hi : ℝ}, 0 ≤ q → q ≤ r → r < hi →
      (∀ i, hi ≤ (Z i).stop) → (∀ i, (Z i).target-r ≤ H) →
      ∀ᵐy:HeatCircle∂haarAddCircle,
        heatRow Z r y∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
          (NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target)
            (fun i=>(Z i).center) q)).range ∧
        sqrt (scoreVariance
          (NativeFirstScoreReserve.covariance P (fun i=>(Z i).stop) (fun i=>(Z i).target)
            (fun i=>(Z i).center) q) (heatRow Z r y))≤
          sqrt (C/((P.lower/8)*(hi-r)))*
            ∑i,sqrt ‖ProfileVariance.heatPhysical (4*((Z i).target-r)) (Z i).center y‖:=by
  obtain ⟨H,C,hH,hC,hV⟩:=FullFutureDampedHeat.weighted_sqrt_heat_envelope n
  refine ⟨H,C,hH,hC,?_⟩
  intro P Z hages q r hi hq hqr hrhi hstop hsmall
  have hell:0<NativeFirstScoreReserve.floor P:=by
    have :=P.lower_pos
    unfold NativeFirstScoreReserve.floor
    positivity
  have hh:=hV Z hages hq hqr hrhi (le_refl (0:ℝ)) hstop hsmall
    (fun _=>NativeFirstScoreReserve.floor P) measurable_const hell (fun _=>⟨le_rfl,le_rfl⟩)
  have he(y:HeatCircle):weightedHeatRow 0 Z q r y=heatRow Z r y:=by
    apply PiLp.ext
    intro i
    simp only [weightedHeatRow,diagonal_apply,weights,neg_zero,zero_mul,exp_zero,one_mul]
  simpa only [he,NativeFirstScoreReserve.covariance,NativeFirstScoreReserve.floor] using hh

end SHE.NativeReserveRowEnvelope
