module

public import SHE.FiniteItoBlockMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.FiniteItoBlockRows
open MeasureTheory GaussianIncrement PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem rows_ae {n : ℕ} (c : Fin n→ℝ) (R : Fin (n+n)→Process (E := C) 𝓕 μ H) :
    ∀ᵐ p ∂energyMeasure μ H,∀ i,
      FiniteItoBlockMap.rows 𝓕 μ H c R i p=R (Fin.castAdd n i) p+c i • R (Fin.natAdd n i) p := by
  have ha (i : Fin n) := ae_eq_of_ae_eq_trim (Lp.coeFn_add (R (Fin.castAdd n i)) (c i • R (Fin.natAdd n i)))
  have hs (i : Fin n) := ae_eq_of_ae_eq_trim (Lp.coeFn_smul (c i) (R (Fin.natAdd n i)))
  filter_upwards [ae_all_iff.mpr ha,ae_all_iff.mpr hs] with p ha hs i
  have hh := ha i
  have hr := hs i
  change (R (Fin.castAdd n i)+c i • R (Fin.natAdd n i)) p=
    R (Fin.castAdd n i) p+(c i • R (Fin.natAdd n i)) p at hh
  change (c i • R (Fin.natAdd n i)) p=c i • R (Fin.natAdd n i) p at hr
  exact hh.trans (congrArg (fun v => R (Fin.castAdd n i) p+v) hr)

end SHE.FiniteItoBlockRows
