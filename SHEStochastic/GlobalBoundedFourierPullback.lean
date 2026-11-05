module

public import SHEStochastic.GlobalBoundedFourierRecognition
public import SHEStochastic.BoundedFourierPullback
public import SHEStochastic.CylindricalProcessPullback

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.GlobalBoundedFourierPullback
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω Ξ V ι : Type*} [mΩ : MeasurableSpace Ω] [mΞ : MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {F : Filtration ℝ≥0 mΩ} {D : Filtration ℝ≥0 mΞ}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  (π : Ξ → Ω) (hπ : MeasurePreserving π ν μ) (hfil : ∀ t, @Measurable Ξ Ω (D t) (F t) π)
  (W : ℝ≥0 → Ω → RealL2) (hW : StronglyMeasurable[F.predictable] (Function.uncurry W))
  {G : ℝ → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)
  (B : ℝ≥0) (hb : ∀ z, ‖G z‖ ≤ B)

local instance : MeasurableSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := borel _
local instance : BorelSpace (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) := ⟨rfl⟩

open BoundedFourierPullback

include hπ in
/-- Native Fourier equations survive a measure-preserving filtered
pullback, including completion of the underlying probability space. -/
theorem equation (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family D ν H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi))))
    (hDriver : ∀ i t z, Q.W i t z = P.W i t (π z)) (ξ : Ω → RealL2)
    (hEquation : GlobalBoundedFourierRecognition.FourierEquation F μ H W hW hG hβ hβ1 B hb
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) ξ) :
    GlobalBoundedFourierRecognition.FourierEquation D ν H (state π W) (predictable π hfil W hW)
      hG hβ hβ1 B hb (FiniteCylindricalIto.terminalIto Q.toCoordinates e) (ξ ∘ π) := by
  letI : SecondCountableTopology (Lp V 2 (haarAddCircle (T := 2 * Real.pi))) :=
    e.repr.toHomeomorph.secondCountableTopology
  intro T hTH a n
  let u := BoundedFourierInput.input F μ H W hW hG hβ hβ1 B hb a n
  let v := BoundedFourierInput.input D ν H (state π W) (predictable π hfil W hW) hG hβ hβ1 B hb a n
  have hp : MeasurePreserving (FilteredPullback.timeMap π) (energyMeasure ν H) (energyMeasure μ H) :=
    (MeasurePreserving.id (PredictableL2.timeMeasure H)).prod hπ
  have hr : StoppedItoInputs.stop D ν H T v =ᵐ[energyMeasure ν H]
      fun p ↦ (LinearIsometry.id : Lp V 2 (haarAddCircle (T := 2 * Real.pi)) →ₗᵢ[ℝ] _)
        (StoppedItoInputs.stop F μ H T u (FilteredPullback.timeMap π p)) := by
    filter_upwards [StoppedItoInputs.stop_ae D ν H T v,
      hp.quasiMeasurePreserving.ae (StoppedItoInputs.stop_ae F μ H T u),
      input_ae π hπ hfil W hW hG hβ hβ1 B hb a n] with p hn ho hi
    rw [hn, ho]
    change (StoppedItoInputs.before T).indicator v p =
      (StoppedItoInputs.before T).indicator u (FilteredPullback.timeMap π p)
    by_cases ht : (p.1 : ℝ) < T
    · simpa only [StoppedItoInputs.before, FilteredPullback.timeMap, Set.indicator_apply,
        Set.mem_setOf_eq, ht, ite_true] using hi
    · simp only [StoppedItoInputs.before, FilteredPullback.timeMap, Set.indicator_apply,
        Set.mem_setOf_eq, ht, ite_false]
  have hj := CylindricalPullback.process_naturality π hπ hfil P Q e e LinearIsometry.id id
    (fun _ ↦ rfl) hDriver (StoppedItoInputs.stop F μ H T u) (StoppedItoInputs.stop D ν H T v) hr
  filter_upwards [hπ.quasiMeasurePreserving.ae (hEquation T hTH a n), hj] with z he hj
  exact he.trans hj.symm

end SHEStochastic.GlobalBoundedFourierPullback
