module

public import SHEStochastic.NativePredictableRotation
public import SHEStochastic.NativePhysicalState
public import SHE.HaarInnovationIto
public import SHE.RealRootMultiplier
public import SHE.ScalarHaarHeatRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativePhysicalInnovation
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation SHE.StoppedFourier
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace (Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

variable {Ω V ι κ : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [Countable ι] [DecidableEq ι] [Countable κ] [DecidableEq κ]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {ell cap : ℝ} (hell : 0 < ell)
  (f : ℝ≥0 × Ω → EllipticField ell cap) (hf : StronglyMeasurable[F.predictable] f)
  (r : RealHaarInput →ₗᵢ[ℝ] V)

/-- Physical pointwise square-root noise is carried into the common
Haar noise by the existing innovation, with the exact circle convention. -/
def field (p : ℝ≥0 × Ω) : Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) →ₗᵢ[ℝ] V :=
  r.comp ((HaarInnovationIto.field hell f p).comp NativePhysicalState.pull)

include hf in
theorem field_measurable : @Measurable
    ((ℝ≥0 × Ω) × Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) V
    (F.predictable.prod (borel _)) ‹MeasurableSpace V› (fun p ↦ field hell f r p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hp : Measurable (fun p : (ℝ≥0 × Ω) ×
      Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) ↦
        (p.1, NativePhysicalState.pull p.2)) :=
    measurable_fst.prodMk (NativePhysicalState.pull.continuous.measurable.comp measurable_snd)
  have hh := (HaarInnovationIto.field_measurable F hell f hf).comp hp
  exact r.continuous.measurable.comp hh

theorem pull_push (v : RealL2) : NativePhysicalState.pull (NativePhysicalState.push v) = v := by
  apply NativePhysicalState.push.injective
  exact NativePhysicalState.push_pull _

/-- This identity uses the literal physical heat row, not just equality
of covariance or of the marginal noise laws. -/
theorem heat_row (p : ℝ≥0 × Ω) {T s : ℝ} (hs : s < T) (x : HeatCircle) :
    field hell f r p (NativePhysicalState.push
      (RealRootMultiplier.action hell (f p) (ScalarHaarHeatRows.test (T-s) x))) =
        r (NativeObservationCovariance.row hell (f p) T s x) := by
  change r (fieldRealInnovation ell cap hell (f p)
    (NativePhysicalState.pull (NativePhysicalState.push _))) = _
  rw [pull_push]
  congr 1
  change fieldRealInnovation ell cap hell (f p)
    (realPart (CircleMultiplier.rootEquivalence (f p).1 ell cap hell
      ((f p).2.2.mono (fun _ h ↦ h.1)) ((f p).2.2.mono (fun _ h ↦ h.2))
        (realEmbed (ScalarHaarHeatRows.test (T-s) x)))) = _
  rw [← realFactorAnalysis_innovation]
  rw [ScalarHaarHeatRows.embed_test (sub_pos.mpr hs)]
  rfl

/-- An actual physical cylindrical Brownian family whose native
integral is the common-Haar integral under the solution-dependent
innovation. The seven native stochastic packages therefore apply. -/
theorem exists_family (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ V)
    (b : HilbertBasis κ ℝ (Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Q : FiniteScalarIto.Family F μ H κ,
      ∀ u : Process (E := Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) F μ H,
        (FiniteCylindricalIto.terminalIto Q.toCoordinates b).integral u =
          (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
            (PredictableItoRotation.processIsometry F μ H (field hell f r)
              (field_measurable F hell f hf r) u) :=
  NativePredictableRotation.exists_family P e b (field hell f r) (field_measurable F hell f hf r) hnull

end SHEStochastic.NativePhysicalInnovation
