module

public import SHE.WeightedMeanFactorization
public import SHE.SignedKernelColumns
public import SHE.QuarterKernelTimes

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers GaussianConvolution HistoryProductMeasure SmoothCylinders NormalizedKernelSplit NativeRandomKernel
open scoped ENNReal
local instance weightedMeanOperator_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance weightedMeanOperator_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance weightedMeanOperator_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

def weightedField (k : ℕ) (Λ q r : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k)) (t : Fin k → ℝ) : X × Space → ℂ :=
  fun z => weightedSpatial L k Λ q r m t z.1 z.2.1 z.2.2

theorem weightedField_measurable (k : ℕ) (Λ q r : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2)) (t : Fin k → ℝ) :
    Measurable (weightedField L k Λ q r m t) :=
  weightedSpatial_variable_measurable L k Λ (fun _ : X => q) (fun _ => r)
    measurable_const measurable_const m hm (fun _ => t) measurable_const

/-- Exact bounded-operator factorization of the stop-weighted physical
kernel; the right heat acts on the signed input before absolute values. -/
theorem weighted_operator_split (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q r : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (hqr : q≤r) (hr : r<fixedTerminal (R:=R) T k t) (x : X) :
    integralOperator (weightedField L k Λ q q m t) x=
      (integralOperator (weightedField L k Λ q r m t) x).comp
        (circleHeatOperator (r-q) (sub_nonneg.mpr hqr)) := by
  obtain ⟨Bq,hBq,hboundq⟩ := weightedSpatial_uniform_bound L (X:=X) T hT k hΛ q q t
  obtain ⟨Br,hBr,hboundr⟩ := weightedSpatial_uniform_bound L (X:=X) T hT k hΛ q r t
  have hFq := weightedField_measurable L k Λ q q m hm t
  have hFr := weightedField_measurable L k Λ q r m hm t
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [integralOperator_ae hFq hBq (fun z y p => hboundq m z y p) x v,
    integralOperator_ae hFr hBr (fun z y p => hboundr m z y p) x
      (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v)] with p hpq hpr
  change integralOperator (weightedField L k Λ q q m t) x v p=
    integralOperator (weightedField L k Λ q r m t) x (circleHeatOperator (r-q) (sub_nonneg.mpr hqr) v) p
  rw [hpq,hpr]
  exact weightedSpatial_integral_split L T hT k hΛ q r m hm t hqr hr x p v

/-- The actual weighted raw same-Haar trace equals the separated trace,
with heat parameter 2(r-q). Bessel mass is independent of damping Λ. -/
theorem weighted_raw_trace_eq_separated (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) {Λ : ℝ} (hΛ : 0≤Λ) (q r : ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (hqr : q≤r) (hr : r<fixedTerminal (R:=R) T k t)
    {mass ρ : ℝ} (hmass : 1≤mass) (hρ : 0≤ρ) (c d : CircleHeat.CircleL2) (x : X) :
    (∑' i : FiniteHaar.HaarNode,‖OneInputOperator.besselHalf mass ρ hmass hρ
      (integralOperator (weightedField L k Λ q q m t) x
        (CircleNormalization.push (FiniteHaar.globalHaarColumn i d-FiniteHaar.globalHaarColumn i c)))‖^2)=
      SignedKernelEnergy.energy (weightedField L k Λ q r m t) mass ρ (2*(r-q)) hmass hρ
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hqr)) c d x := by
  unfold SignedKernelEnergy.energy
  simp only [show 2*(r-q)/2=r-q by ring]
  apply tsum_congr
  intro i
  rw [weighted_operator_split L T hT k hΛ q r m hm t hqr hr x,ContinuousLinearMap.comp_apply]

end SHE.ActualMeanKernel
