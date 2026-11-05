module

public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ActualMeanKernel
open MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  HistoryProductMeasure
local instance actualMeanKernelCongruence_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ} (L : Level R X n)

/-- Equality of Gaussian means is needed only where the literal
weighted direction kernel is active. -/
theorem weightedPoint_mean_congr (k : ℕ) (Λ q r : ℝ)
    (m m' : History X k→WordRecursion.State (n+k))
    (hm : ∀ h,q<(carrier L k).terminal h→m h=m' h) (h : History X k) (y : HeatCircle) :
    weightedPoint L k Λ q r m h y=weightedPoint L k Λ q r m' h y := by
  classical
  unfold weightedPoint
  split_ifs with ha
  · rw [hm h ha.1]
  · rfl

theorem weightedSpatial_mean_congr (k : ℕ) (Λ q r : ℝ)
    (m m' : History X k→WordRecursion.State (n+k))
    (hm : ∀ h,q<(carrier L k).terminal h→m h=m' h)
    (t : Fin k→ℝ) (y : HeatCircle) (x : X) :
    weightedSpatial L k Λ q r (fun _ : Unit=>m) t () y x=
      weightedSpatial L k Λ q r (fun _ : Unit=>m') t () y x := by
  unfold weightedSpatial
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  exact weightedPoint_mean_congr L k Λ q r m m' hm _ _

end SHE.ActualMeanKernel
