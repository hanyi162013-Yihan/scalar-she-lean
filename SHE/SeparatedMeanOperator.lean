module

public import SHE.SeparatedMeanFactorization
public import SHE.SignedKernelColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders NormalizedKernelSplit NativeRandomKernel
open scoped ENNReal
local instance separatedMeanOperator_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance separatedMeanOperator_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance separatedMeanOperator_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

def rowField (k : ℕ) (q r : ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (t : Fin k → ℝ) : X × Space → ℂ :=
  fun z => rowSpatial L k q r m t z.1 z.2.1 z.2.2

theorem rowField_measurable (k : ℕ) (q r : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2)) (t : Fin k → ℝ) :
    Measurable (rowField L k q r m t) :=
  rowSpatial_variable_measurable L k (fun _ : X => q) (fun _ : X => r)
    measurable_const measurable_const m hm (fun _ => t) measurable_const

theorem rowField_same (k : ℕ) (q : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k)) (t : Fin k → ℝ) :
    rowField L k q q m t=field L k q m t := by
  funext z
  simp only [rowField,field,rowSpatial_same]

/-- Exact operator factorization of the original terminal point kernel.
The Gaussian covariance/current mean remain at q, while the kernel row is
moved to r and the genuine right heat is S_(r-q). -/
theorem row_operator_split (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q r : ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (hqr : q ≤ r) (hr : r < fixedTerminal (R:=R) T k t) (x : X) :
    integralOperator (field L k q m t) x=
      (integralOperator (rowField L k q r m t) x).comp
        (circleHeatOperator (r-q) (sub_nonneg.mpr hqr)) := by
  obtain ⟨Bq,hBq,hboundq⟩ := rowSpatial_uniform_bound L (X:=X) T hT k q q t
  obtain ⟨Br,hBr,hboundr⟩ := rowSpatial_uniform_bound L (X:=X) T hT k q r t
  have hFq := rowField_measurable L k q q m hm t
  have hFr := rowField_measurable L k q r m hm t
  have hrowq := fun z y p => hboundq m z y p
  have hrowr := fun z y p => hboundr m z y p
  rw [←rowField_same L k q m t]
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [integralOperator_ae hFq hBq hrowq x v,
    integralOperator_ae hFr hBr hrowr x (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v)] with p hpq hpr
  change integralOperator (rowField L k q q m t) x v p=
    integralOperator (rowField L k q r m t) x (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v) p
  rw [hpq,hpr]
  exact rowSpatial_integral_split L T hT k q r m hm t hqr hr x p v

/-- The raw signed-noise trace is exactly the existing separated trace,
with parameter 2(r-q); no extra smoothing of the true noise row occurs. -/
theorem raw_trace_eq_separated (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q r : ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (hqr : q ≤ r) (hr : r < fixedTerminal (R:=R) T k t)
    {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (c d : CircleHeat.CircleL2) (x : X) :
    (∑' i : FiniteHaar.HaarNode,‖OneInputOperator.besselHalf Λ ρ hΛ hρ
      (integralOperator (field L k q m t) x
        (CircleNormalization.push (FiniteHaar.globalHaarColumn i d-FiniteHaar.globalHaarColumn i c)))‖^2)=
      SignedKernelEnergy.energy (rowField L k q r m t) Λ ρ (2*(r-q)) hΛ hρ
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hqr)) c d x := by
  unfold SignedKernelEnergy.energy
  simp only [show 2*(r-q)/2=r-q by ring]
  apply tsum_congr
  intro i
  rw [row_operator_split L T hT k q r m hm t hqr hr x,ContinuousLinearMap.comp_apply]

end SHE.ActualMeanKernel
