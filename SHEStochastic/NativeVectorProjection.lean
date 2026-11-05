module

public import SHEStochastic.NativeVectorIntegralVersion
public import SHE.GaussianCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeVectorProjection
open MeasureTheory Set SHE SHE.PredictableL2 SHE.GaussianCoordinates SHE.GaussianIncrement
open TopologicalSpace
open scoped NNReal ENNReal

/-- Pointwise modifications with continuous paths agree for all times
on one event, by countable dense testing. No time-dependent exceptional
set remains when an observation history is extended. -/
theorem continuous_versions {Ω T E : Type*} [MeasurableSpace Ω] [TopologicalSpace T] [SeparableSpace T]
    [TopologicalSpace E] [T2Space E] (μ : Measure Ω) (X Y : T → Ω → E)
    (hX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω)) (hY : ∀ᵐ ω ∂μ, Continuous (fun t => Y t ω))
    (he : ∀ t, X t =ᵐ[μ] Y t) : ∀ᵐ ω ∂μ, ∀ t, X t ω=Y t ω := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense T
  letI : Countable D := hDc.to_subtype
  filter_upwards [hX,hY,ae_all_iff.mpr (fun t : D => he t)] with ω hx hy hω t
  have h : EqOn (fun t => X t ω) (fun t => Y t ω) D := fun t ht => hω ⟨t,ht⟩
  exact h.closure hx hy (by rw [hDd.closure_eq]; trivial)

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  {k ell : ℕ}

/-- Selecting old coordinates commutes exactly with the literal native
vector integral, allowing repeated observation coordinates. -/
theorem integral (J : StandardTerminalIto (C := C) F μ H) (g : Fin k → Fin ell)
    (z : State ell) (R : Fin ell → Process (E := C) F μ H) (t : ℝ≥0) (ω : Ω) :
    projection g (StandardFiniteIto.vectorIntegral F μ H J z R t ω)=
      StandardFiniteIto.vectorIntegral F μ H J (projection g z) (fun i => R (g i)) t ω := by
  ext i
  rfl

/-- Coordinate retention also holds for versions whose paths are
continuous almost surely. This is the form produced by joint parameter
constructions. -/
theorem ae_versions (J : StandardTerminalIto (C := C) F μ H) (g : Fin k → Fin ell)
    (z : State ell) (R : Fin ell → Process (E := C) F μ H)
    (X : ℝ≥0 × Ω → State k) (Y : ℝ≥0 × Ω → State ell)
    (hX : ∀ᵐ ω ∂μ, Continuous (fun t => X (t,ω)))
    (hY : ∀ᵐ ω ∂μ, Continuous (fun t => Y (t,ω)))
    (hx : ∀ t, (fun ω => X (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H J (projection g z) (fun i => R (g i)) t)
    (hy : ∀ t, (fun ω => Y (t,ω)) =ᵐ[μ] StandardFiniteIto.vectorIntegral F μ H J z R t) :
    ∀ᵐ ω ∂μ, ∀ t, X (t,ω)=projection g (Y (t,ω)) := by
  apply continuous_versions μ (fun t ω => X (t,ω)) (fun t ω => projection g (Y (t,ω))) hX
    (hY.mono (fun ω hω => (projection g).continuous.comp hω))
  intro t
  filter_upwards [hx t,hy t] with ω hω hη
  rw [hω,hη,integral]

/-- Continuous native histories constructed separately at successive
vector word sizes retain the same old observations simultaneously at
every time. This is derived from actual integral representations. -/
theorem versions (J : StandardTerminalIto (C := C) F μ H) (g : Fin k → Fin ell)
    (z : State ell) (R : Fin ell → Process (E := C) F μ H)
    (X : ℝ≥0 × Ω → State k) (Y : ℝ≥0 × Ω → State ell)
    (hX : ∀ ω, Continuous (fun t => X (t,ω))) (hY : ∀ ω, Continuous (fun t => Y (t,ω)))
    (hx : ∀ t, (fun ω => X (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H J (projection g z) (fun i => R (g i)) t)
    (hy : ∀ t, (fun ω => Y (t,ω)) =ᵐ[μ] StandardFiniteIto.vectorIntegral F μ H J z R t) :
    ∀ᵐ ω ∂μ, ∀ t, X (t,ω)=projection g (Y (t,ω)) := by
  apply continuous_versions μ (fun t ω => X (t,ω)) (fun t ω => projection g (Y (t,ω)))
    (Filter.Eventually.of_forall hX)
    (Filter.Eventually.of_forall (fun ω => (projection g).continuous.comp (hY ω)))
  intro t
  filter_upwards [hx t,hy t] with ω hω hη
  rw [hω,hη,integral]

end SHEStochastic.NativeVectorProjection
