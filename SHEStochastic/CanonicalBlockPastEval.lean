module

public import SHEStochastic.MatrixGlobalBlockPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.CanonicalBlockPastEval
open MeasureTheory Set SHE.CanonicalStateDriverFiltration
open scoped NNReal
variable {E ι : Type*} [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem state (H s t : ℝ≥0) (x : SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    SHE.CanonicalStateDriverFiltration.state H t (history H s x)=
      SHE.CanonicalStateDriverFiltration.state H (min t s) x := by
  change x.1 (SHE.CanonicalFutureStateDriver.stopTime (clock H s) (clock H t))=x.1 (clock H (min t s))
  congr 1
  apply Subtype.ext
  change min (min (t : ℝ) H) (min (s : ℝ) H)=min (min (t : ℝ) (s : ℝ)) H
  rw [min_min_min_comm,min_self]

theorem coordinate (H s t : ℝ≥0) (i : ι)
    (x : SHE.CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :
    SHE.CanonicalStateDriverFiltration.coordinate H i t (history H s x)=
      SHE.CanonicalStateDriverFiltration.coordinate H i (min t s) x := by
  change x.2 i (SHE.CanonicalFutureStateDriver.stopTime (clock H s) (clock H t))=x.2 i (clock H (min t s))
  congr 1
  apply Subtype.ext
  change min (min (t : ℝ) H) (min (s : ℝ) H)=min (min (t : ℝ) (s : ℝ)) H
  rw [min_min_min_comm,min_self]

end SHEStochastic.CanonicalBlockPastEval
