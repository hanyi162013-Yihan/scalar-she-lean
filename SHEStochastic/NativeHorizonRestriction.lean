module

public import SHEStochastic.FiniteScalarIto

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHEStochastic.NativeHorizonRestriction
open MeasureTheory SHE
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} {H : ℝ≥0}

/-- Shorten the terminal interval while retaining the actual coordinate
processes, their adaptation and their continuous paths. -/
def family (P : FiniteScalarIto.Family F μ H ι) (K : ℝ≥0) (hK : K ≤ H) :
    FiniteScalarIto.Family F μ K ι where
  W := P.W
  adapted := P.adapted
  continuous := P.continuous
  law n a := ⟨fun t ht ↦ (P.law n a).1 t (fun i ↦ (ht i).trans hK),
    fun s t hst ht ↦ (P.law n a).2 s t hst (ht.trans hK)⟩

end SHEStochastic.NativeHorizonRestriction
