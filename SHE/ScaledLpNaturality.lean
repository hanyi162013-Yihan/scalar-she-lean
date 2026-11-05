module

public import SHE.ScaledLpPull

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.ScaledLpPull
open MeasureTheory Filter
open scoped ENNReal
variable {A B E D : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable (μ : Measure A) (ν : Measure B) (c : ℝ) (hc : 0<c)
variable (g : A→B) (hg : MeasurePreserving g (ENNReal.ofReal c • μ) ν)
variable (he : MeasurableEmbedding g)

/-- A bounded linear map commutes with the actual normalized L²
pullback, including its square-root Jacobian. -/
theorem isometry_compLpL (L : E→L[ℝ]D) (v : Lp E 2 ν) :
    (L.compLpL 2 μ) (isometry μ ν c hc g hg he v)=
      isometry μ ν c hc g hg he ((L.compLpL 2 ν) v) := by
  apply Lp.ext
  have hL := ae_comp μ ν c hc g hg (L.coeFn_compLpL v)
  filter_upwards [L.coeFn_compLpL (isometry μ ν c hc g hg he v),
    pull_ae μ ν c hc g hg v,pull_ae μ ν c hc g hg ((L.compLpL 2 ν) v),hL]
    with x hout hv hmap hin
  rw [hout]
  change L (pull μ ν c hc g hg v x)=pull μ ν c hc g hg ((L.compLpL 2 ν) v) x
  rw [hv,hmap]
  change L (Real.sqrt c • v (g x))=Real.sqrt c • ((L.compLpL 2 ν) v) (g x)
  rw [hin,L.map_smul]

end SHE.ScaledLpPull
