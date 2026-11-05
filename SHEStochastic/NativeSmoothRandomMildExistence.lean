module

public import SHEStochastic.SmoothRandomMildExistence
public import SHEStochastic.NativeHilbertBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeSmoothRandomMildExistence
open MeasureTheory SHE SHE.PredictableL2 SHE.LowBands SHE.HilbertColumns SHE.FiniteHaar
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology StateL2 := inferInstance
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

variable {Ω V ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι] [Countable κ]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ V)
  (r : Space HaarNode ℝ →ₗᵢ[ℝ] V) (b : HilbertBasis κ ℝ StateL2)

def integral : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := StateL2) F μ H :=
  HilbertTerminalIto.terminalIto F μ H b
    (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r)

/-- Smooth approximation existence with random L2 initial data, using
the actual native integral. Both terminal Hilbert integration and BDG
are constructed from the Brownian coordinates; no stochastic package
is assumed as a new input to this existence theorem. -/
theorem exists_mild (hH : (H : ℝ) ≤ 1) (hpos : 0 < H)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    {a : ℝ → ℝ} (ha : Measurable a) {ell cap K β : ℝ}
    (hell : 0 < ell) (hb : ∀ z, ell ≤ a z ∧ a z ≤ cap)
    (hβ : 0 < β) (hK : 0 ≤ K) (hholder : ∀ z w, |a z - a w| ≤ K * |z - w| ^ β)
    {L : ℝ≥0} (hLip : LipschitzWith L (fun z ↦ (a z : ℂ)))
    (Z : Ω → StateL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ) :
    ∃ U : ℝ≥0 → Ω → StateL2, (∀ sample, Continuous (fun t ↦ U t sample)) ∧
      StronglyMeasurable[F.predictable] (Function.uncurry U) ∧
      ∃ hfield : StronglyMeasurable[F.predictable]
        (ContinuousHeatMild.coefficientFunction ha hell hb U),
        ∀ (t : ℝ≥0) (ht : t ≤ H), U t =ᵐ[μ] fun sample ↦
          RealHeat.realHeat (t : ℝ) (Z sample) +
            DampedFixedIntegral.value F μ H hH (Λ := 0) (by norm_num) hell
              (hell.le.trans ((hb 0).1.trans (hb 0).2))
              (ContinuousHeatMild.coefficientFunction ha hell hb U) hfield
              (integral F μ H P e r b) t ht sample :=
  SmoothRandomMildExistence.exists_mild F μ H hH ha hell hb hβ hK hholder
    (integral F μ H P e r b) (NativeScalarBDG.constant 3)
    (NativeHilbertBDG.hilbertBDG16 P e r b) hpos hnull hLip Z hZ₀ hZ

end SHEStochastic.NativeSmoothRandomMildExistence
