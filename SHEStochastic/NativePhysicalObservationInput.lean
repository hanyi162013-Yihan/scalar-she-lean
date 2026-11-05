module

public import SHEStochastic.NativePhysicalInnovation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativePhysicalObservationInput
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

variable {Ω V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {ell cap : ℝ} (hell : 0 < ell)
  (f : ℝ≥0 × Ω → EllipticField ell cap) (hf : StronglyMeasurable[F.predictable] f)

/-- Decode every actual predictable Haar input to physical scalar
noise. Both maps are existing L2 isometries, so no new integrability
construction is needed for the heat rows. -/
def decode : Process (E := RealHaarInput) F μ H →ₗᵢ[ℝ]
    Process (E := Lp ℝ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi))) F μ H := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) NativePhysicalState.push).comp
    (HaarInnovationIto.inverseRotation F μ H hell f hf)

theorem decode_ae (u : Process (E := RealHaarInput) F μ H) :
    decode F μ H hell f hf u =ᵐ[energyMeasure μ H]
      fun p ↦ NativePhysicalState.push ((fieldRealInnovation ell cap hell (f p)).symm (u p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  filter_upwards [ae_eq_of_ae_eq_trim (L2HilbertSum.lift_ae
    ((energyMeasure μ H).trim (predictable_le_product F)) NativePhysicalState.push
    (HaarInnovationIto.inverseRotation F μ H hell f hf u)),
    HaarInnovationIto.inverseRotation_ae F μ H hell f hf u] with p hp hu
  exact hp.trans (congrArg NativePhysicalState.push hu)

theorem encode_decode (r : RealHaarInput →ₗᵢ[ℝ] V) (u : Process (E := RealHaarInput) F μ H) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    PredictableItoRotation.processIsometry F μ H (NativePhysicalInnovation.field hell f r)
      (NativePhysicalInnovation.field_measurable F hell f hf r) (decode F μ H hell f hf u) =
        L2HilbertSum.lift ((energyMeasure μ H).trim (predictable_le_product F)) r u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PredictableItoRotation.processIsometry_ae F μ H (NativePhysicalInnovation.field hell f r)
    (NativePhysicalInnovation.field_measurable F hell f hf r) (decode F μ H hell f hf u),
    decode_ae F μ H hell f hf u,
    ae_eq_of_ae_eq_trim (L2HilbertSum.lift_ae
      ((energyMeasure μ H).trim (predictable_le_product F)) r u)] with p hp hd hr
  rw [hp, hd, hr]
  change r (fieldRealInnovation ell cap hell (f p)
    (NativePhysicalState.pull (NativePhysicalState.push _))) = _
  rw [NativePhysicalInnovation.pull_push, LinearIsometryEquiv.apply_symm_apply]

/-- Explicit square-root heat rows represented by the decoded input,
including its exact deterministic stopping mask. -/
theorem observation_ae (hcap : 0 ≤ cap) {T t : ℝ} (ht : t < T) (x : HeatCircle) :
    decode F μ H hell f hf (NativeObservationProcess.process F μ H hell hcap f hf ht x) =ᵐ[energyMeasure μ H]
      fun p ↦ if (p.1 : ℝ) < t then NativePhysicalState.push
        (RealRootMultiplier.action hell (f p) (ScalarHaarHeatRows.test (T-(p.1 : ℝ)) x)) else 0 := by
  filter_upwards [decode_ae F μ H hell f hf (NativeObservationProcess.process F μ H hell hcap f hf ht x),
    NativeObservationProcess.process_ae F μ H hell hcap f hf ht x] with p hp hr
  rw [hp, hr, NativeObservationProcess.integrand_eq hell f ht]
  by_cases hs : (p.1 : ℝ) < t
  · rw [if_pos hs, if_pos hs]
    congr 1
    have hd := RealRootMultiplier.decode_analysis hell (f p) (ScalarHaarHeatRows.test (T-(p.1 : ℝ)) x)
    rw [ScalarHaarHeatRows.embed_test (sub_pos.mpr (hs.trans ht))] at hd
    exact hd
  · rw [if_neg hs, if_neg hs, map_zero, map_zero]

end SHEStochastic.NativePhysicalObservationInput
