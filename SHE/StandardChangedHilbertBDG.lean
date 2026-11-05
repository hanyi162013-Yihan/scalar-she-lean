module

public import SHE.StandardRecognizedHilbertBDG
public import SHE.GirsanovTransportWitness
public import SHE.NullCompleteFiltration

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE
open MeasureTheory PredictableL2 FiniteHaar OrthogonalItoChannels
open scoped NNReal

local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩

/-- Hilbert BDG on precisely the changed integrals used by the
comparison proof. The original map, capped control, equivalent changed
measure and SAME-integral transport witness are retained explicitly.
This avoids quantifying over unrelated abstract terminal isometries. -/
def StandardChangedHilbertBDG {Ω : Type*} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) F μ H) : Prop :=
  ∀ (Q : Measure Ω) [IsProbabilityMeasure Q]
    (K : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) F Q H)
    (T : GirsanovTransportWitness F μ Q H J K),
    μ ≪ Q → Q ≪ μ → NullCompleteFiltration.ContainsNullSets F μ →
    StandardTerminalPastLocality J → 0 < H → (H : ℝ) ≤ 1 →
    (∀ᵐ sample ∂μ, StochasticExponential.bracket F μ H T.control sample ≤ 1) →
    Q = ExponentialChangeMeasure.measure μ (fun sample ↦ J.integral T.control sample)
      (StochasticExponential.bracket F μ H T.control) →
    StandardRecognizedHilbertBDG F Q H K

end SHE
