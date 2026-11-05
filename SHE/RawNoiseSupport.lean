module

public import SHE.QuarterSpatialEvent
public import SHE.MixedNativeJointNoise

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeRandomKernel
open Set MeasureTheory StoppedFourier NormalizedKernelSplit
open scoped ENNReal
local instance rawNoiseSupport_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X]

theorem integralOperator_zero (x : X) : integralOperator (0 : X × Space → ℂ) x=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [integralOperator_ae (F:=0) measurable_const le_rfl (fun _ _ _ => by simp) x v,
    Lp.coeFn_zero (E:=ℂ) (p:=2) (μ:=AddCircle.haarAddCircle (T:=2*Real.pi))] with y hy hz
  change integralOperator (0 : X × Space → ℂ) x v y=(0:CircleL2) y
  rw [hz]
  simpa only [Pi.zero_apply,zero_mul,integral_zero] using hy

theorem integralOperator_zero_section {F : X × Space → ℂ} (x : X)
    (hF : ∀ p,F (x,p)=0) : integralOperator F x=0 := by
  rw [NativeRealNoise.integralOperator_section]
  have hz : (fun z : Unit × Space => F (x,z.2))=0 := funext (fun z => hF z.2)
  rw [hz]
  exact integralOperator_zero ()

end SHE.NativeRandomKernel

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories CutoffCarriers
  HistoryProductMeasure QuarterSpatialEvent NativeRandomKernel PhysicalParentGeometry
local instance rawNoiseSupport_meanNativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

/-- Every old-history section outside the genuine active ordered domain
is literally zero, before any AE or moment argument. -/
theorem spatial_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) (x : X) (y p : HeatCircle) : spatial L k q m t x y p=0 := by
  have hp (z : Fin k → HeatCircle) :
      point L k q (m x) (separated k (p,t,z)) y=0 := by
    by_cases hs : StrictHistory L k (anchor k t)
    · have hq : ¬q < fixedTerminal (R:=R) T k t := fun h => ha ⟨hs,h⟩
      simp only [point,terminal_separated L T hT,ite_eq_right hq]
    · exact point_zero_of_not_strict L k q (m x) _ y (fun h => hs
        ((FixedHistoryTimeFactors.strict_sections L T hT k t p 0 z (fun _ => 0)).mp h))
  simp only [spatial,hp,integral_zero,Complex.ofReal_zero]

theorem field_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) : field L k q m t=0 := by
  funext z
  exact spatial_zero_of_not_active L T hT k q t m ha z.1 z.2.1 z.2.2

/-- The raw same-Haar Hilbert columns themselves vanish outside active
old times, so the section trace estimate extends to the full old-time
cube without an assumed support theorem. -/
theorem rawColumns_zero_of_not_active (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (q : ℝ) (t : Fin k → ℝ) (m : X → History HeatCircle k → WordRecursion.State (1+k))
    (ha : ¬active L T k q t) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (ell M : ℝ) (hell : 0 < ell) (c d : X → FiniteHaar.EllipticField ell M) (x : X) :
    SignedKernelColumns.rawColumns (field L k q m t) Λ ρ hΛ hρ ell M hell c d x=0 := by
  apply lp.ext
  funext i
  rw [SignedKernelColumns.rawColumns_apply,field_zero_of_not_active L T hT k q t m ha,
    integralOperator_zero]
  simp only [ContinuousLinearMap.zero_apply,map_zero,lp.coeFn_zero,Pi.zero_apply]

end SHE.ActualMeanKernel
