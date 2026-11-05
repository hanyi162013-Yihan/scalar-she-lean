module

public import SHEStochastic.MatrixMildObservations
public import SHEStochastic.MatrixPointTargetContinuity
public import SHEStochastic.VectorStateRepresentative
public import SHEStochastic.HeatEndpointSequence
public import SHE.ObservationTargetContinuity
public import SHEStochastic.MatrixFuturePointMoments

@[expose] public section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixMildEndpoint
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.FiniteHaar
open SHE.DyadicApproximation MatrixInfiniteHaar
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
    (G : MatrixNonlinearCoefficient.Coefficient (Fin n)) (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H ((Fin n) × HaarNode))
    (U : ℝ≥0 × Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (u₀ : Physical (d := Fin n)) (hEq : MatrixContinuousMild.Equation G hH N U hU u₀)
local notation "Q" => NativeMatrixEquation.profile F G U hU
local notation "Qm" => NativeMatrixEquation.profile_measurable F G U hU
local notation "cap" => NativeMatrixEquation.cap G
local notation "cap0" => NativeMatrixEquation.cap_nonneg G
local notation "J" => FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis

/-- The actual nonlinear vector state at positive times has the literal
original-target point-integral representation, spatially almost everywhere.
The zero heat age is proved by a limit in the original native input space;
it is not assumed as an additional mild equation or pointwise version. -/
theorem point_history_random
    (Z : Ω → Physical (d := Fin n)) (hRandom : MatrixRandomMildExistence.Equation G hH N U hU Z) (s : ℝ≥0) (hs0 : 0<s) (hsH : s<H) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      VectorStateRepresentative.native (fun ω => U (s,ω)) (ω,x)=
        VectorHeatMean.mean (Z ω) ((s : ℝ),x)+
          WithLp.toLp 2 (fun a : Fin n => (J).integral
            (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a) ω) := by
  let ε : ℕ → ℝ := fun j => ((H : ℝ)-(s : ℝ))/((j : ℝ)+1)
  have hε (j : ℕ) : 0<ε j := div_pos (sub_pos.mpr hsH) (by positivity)
  have hεle (j : ℕ) : ε j ≤ (H : ℝ)-(s : ℝ) := by
    change ((H : ℝ)-(s : ℝ))/((j : ℝ)+1) ≤ (H : ℝ)-(s : ℝ)
    exact div_le_self (sub_nonneg.mpr (show (s : ℝ)≤(H : ℝ) from hsH.le))
      (show (1 : ℝ)≤(j : ℝ)+1 by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,div_eq_mul_inv,one_div,mul_zero,one_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((H : ℝ)-(s : ℝ)))
  let T : ℕ → ℝ≥0 := fun j => NNReal.mk ((s : ℝ)+ε j) (add_nonneg s.2 (hε j).le)
  have hT (j : ℕ) : T j ≤ H := by change (s : ℝ)+ε j ≤ (H : ℝ); linarith [hεle j]
  have hsT (j : ℕ) : s<T j := by change (s : ℝ)<(s : ℝ)+ε j; linarith [hε j]
  have hT0 : Tendsto T atTop (𝓝 s) := by
    apply NNReal.tendsto_coe.mp
    simpa only [T,NNReal.coe_mk,add_zero] using hε0.const_add (s : ℝ)
  have hUs : Measurable (fun ω => U (s,ω)) :=
    (hU.mono (predictable_le_product F)).measurable.comp (measurable_const.prodMk measurable_id)
  have hi (a : Fin n) : ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      PredictableScalarField.nativeField (VectorStateRepresentative.component (fun ω => U (s,ω)) a) (ω,x)=
        PhysicalProfile.physicalHeatMean (NativeHeatObservation.embed (VectorHeat.coordinates (Z ω) a)) ((s : ℝ),x)+
          (J).integral (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a) ω := by
    apply HeatEndpointSequence.identify_random J (VectorStateRepresentative.component (fun ω => U (s,ω)) a)
      (VectorStateRepresentative.component_measurable _ hUs a) ε hε hε0
      (fun j x => MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s (T j) (hT j) x a)
      (fun x => MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a)
    · intro x
      exact MatrixPointTargetContinuity.tendsto F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s hsH.le s hsH.le le_rfl
        T hT (fun j => (hsT j).le) hT0 x a
    · intro x ω
      exact (ObservationTargetContinuity.continuousAt_heatMean_age
        (show 0<(s : ℝ) from hs0) (NativeHeatObservation.embed (VectorHeat.coordinates (Z ω) a)) x).tendsto.comp
          (NNReal.continuous_coe.tendsto s |>.comp hT0)
    · intro j x
      have ho := MatrixMildObservations.heat_observation_random G hH N U hU Z hRandom s (T j) hsH.le (hT j) (hsT j) x a
      have he : (T j : ℝ)-(s : ℝ)=ε j := by simp only [T,NNReal.coe_mk]; ring
      simp only [VectorHeatObservation.apply_component,he,
        NativeHeatObservation.functional_physical (show 0<(T j : ℝ) from hs0.trans (hsT j))] at ho
      exact ho
  filter_upwards [ae_all_iff.mpr hi] with x hx
  filter_upwards [ae_all_iff.mpr hx] with ω hω
  ext a
  exact hω a


include hEq in
theorem point_history (s : ℝ≥0) (hs0 : 0<s) (hsH : s<H) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      VectorStateRepresentative.native (fun ω => U (s,ω)) (ω,x)=
        VectorHeatMean.mean u₀ ((s : ℝ),x)+
          WithLp.toLp 2 (fun a : Fin n => (J).integral
            (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a) ω) := by
  exact point_history_random G hH N U hU (fun _ => u₀) hEq s hs0 hsH

include hEq in
/-- The current point field minus the actual propagated past state is
the original native future increment. This identifies the random mean
displacement needed by the rough-leaf moment estimates. -/
theorem past_increment (v s : ℝ≥0) (hvs : v<s) (hsH : s<H) :
    ∀ᵐ x ∂AddCircle.haarAddCircle (T := 2*Real.pi), ∀ᵐ ω ∂μ,
      VectorStateRepresentative.native (fun ω => U (s,ω)) (ω,x)-
        VectorHeatObservation.observation ((s : ℝ)-(v : ℝ)) x (U (v,ω))=
          WithLp.toLp 2 (fun a : Fin n => (J).integral
            (MatrixFuturePointMoments.input F μ H hH cap cap0 Q (fun _ => le_rfl) Qm v s hsH.le x a) ω) := by
  have hs0 : 0<s := bot_le.trans_lt hvs
  filter_upwards [point_history G hH N U hU u₀ hEq s hs0 hsH] with x hx
  have hi (a : Fin n) : (fun ω => (J).integral
      (MatrixFuturePointMoments.input F μ H hH cap cap0 Q (fun _ => le_rfl) Qm v s hsH.le x a) ω) =ᵐ[μ]
      fun ω => (J).integral (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a) ω-
        (J).integral (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm v s hsH.le x a) ω := by
    rw [MatrixFuturePointMoments.input_eq_sub F μ H hH cap cap0 Q (fun _ => le_rfl) Qm v s hsH.le hvs.le x a,map_sub]
    exact Lp.coeFn_sub _ _
  have ho (a : Fin n) := MatrixMildObservations.heat_observation G hH N U hU u₀ hEq v s
    (hvs.le.trans hsH.le) hsH.le hvs x a
  filter_upwards [hx,ae_all_iff.mpr hi,ae_all_iff.mpr ho] with ω hp hj hobs
  ext a
  have hpa := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z a) hp
  have hma := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z a)
    (VectorHeatObservation.mean (show 0<(s : ℝ) from hs0) x u₀)
  have hoa := hobs a
  have hja := hj a
  change VectorHeatObservation.observation ((s : ℝ)-(v : ℝ)) x (U (v,ω)) a=
    VectorHeatObservation.observation (s : ℝ) x u₀ a+
      (J).integral (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm v s hsH.le x a) ω at hoa
  change VectorStateRepresentative.native (fun ω => U (s,ω)) (ω,x) a=
    VectorHeatMean.mean u₀ ((s : ℝ),x) a+
      (J).integral (MatrixPointTargetContinuity.process F μ H hH cap cap0 Q (fun _ => le_rfl) Qm s s hsH.le x a) ω at hpa
  change VectorStateRepresentative.native (fun ω => U (s,ω)) (ω,x) a-
    VectorHeatObservation.observation ((s : ℝ)-(v : ℝ)) x (U (v,ω)) a=_
  linarith only [hpa,hma,hoa,hja]

end SHEStochastic.MatrixMildEndpoint
