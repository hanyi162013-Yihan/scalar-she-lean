module

public import SHE.RawNoiseSupport
public import SHE.WeightedMeanOperator

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  HistoryProductMeasure QuarterSpatialEvent NativeRandomKernel PhysicalParentGeometry
local instance weightedNoiseSupport_nativePositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Exact active-domain support of the weighted signed kernel, with an
independent later row time. The statement is pointwise, before moments. -/
theorem weightedSpatial_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (Λ q r : ℝ) (t : Fin k → ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) (x : X) (y p : HeatCircle) :
    weightedSpatial L k Λ q r m t x y p=0 := by
  have hp (z : Fin k → HeatCircle) :
      weightedPoint L k Λ q r (m x) (separated k (p,t,z)) y=0 := by
    by_cases hs : StrictHistory L k (anchor k t)
    · have hq : ¬q<fixedTerminal (R:=R) T k t := fun h => ha ⟨hs,h⟩
      simp only [weightedPoint,terminal_separated L T hT,hq,false_and,ite_false]
    · exact weightedPoint_zero_of_not_strict L k Λ q r (m x) _ y (fun h => hs
        ((FixedHistoryTimeFactors.strict_sections L T hT k t p 0 z (fun _ => 0)).mp h))
  simp only [weightedSpatial,hp,integral_zero,Complex.ofReal_zero]

theorem weightedField_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (Λ q r : ℝ) (t : Fin k → ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) : weightedField L k Λ q r m t=0 := by
  funext z
  exact weightedSpatial_zero_of_not_active L T hT k Λ q r t m ha z.1 z.2.1 z.2.2

/-- The correctly weighted raw common-Haar columns vanish outside the
ordered active old-time domain. This permits extension of section trace
bounds to the entire finite old-time cube. -/
theorem weighted_rawColumns_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (Λ q r : ℝ) (t : Fin k → ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (ell M : ℝ) (hell : 0<ell) (c d : X → FiniteHaar.EllipticField ell M) (x : X) :
    SignedKernelColumns.rawColumns (weightedField L k Λ q r m t) mass ρ hmass hρ ell M hell c d x=0 := by
  apply lp.ext
  funext i
  rw [SignedKernelColumns.rawColumns_apply,weightedField_zero_of_not_active L T hT k Λ q r t m ha,
    integralOperator_zero]
  simp only [ContinuousLinearMap.zero_apply,map_zero,lp.coeFn_zero,Pi.zero_apply]

end SHE.ActualMeanKernel
