module

public import SHE.NativeKernelVariable
public import SHE.SignedKernelEnergy
public import SHE.HilbertColumns
public import SHE.HeatAgeContinuity

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.SignedKernelColumns
open Set MeasureTheory AddCircle Real StoppedFourier NativeRandomKernel NativeSignedHaarProcess
open scoped ENNReal
local instance signedKernelColumns_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance signedKernelColumns_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance signedKernelColumns_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance signedKernelColumns_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance signedKernelColumns_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance signedKernelColumns_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance signedKernelColumns_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance signedKernelColumns_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance signedKernelColumns_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*π)).repr.toHomeomorph.secondCountableTopology
local instance signedKernelColumns_kernelSecondCountable : SecondCountableTopology KernelSpace := Lp.SecondCountableTopology
local instance signedKernelColumns_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance signedKernelColumns_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩

abbrev Space := HilbertColumns.Space FiniteHaar.HaarNode CircleL2
local instance signedKernelColumns_measurable : MeasurableSpace Space := borel Space
local instance signedKernelColumns_borel : BorelSpace Space := ⟨rfl⟩
variable {X : Type*} [MeasurableSpace X]
attribute [local irreducible] HeatAgeContinuity.heat circleHeatOperator

set_option backward.isDefEq.respectTransparency false in
theorem native_heat_measurable (t : X → ℝ) (ht : Measurable t) (ht0 : ∀ z, 0 ≤ t z)
    (v : X → CircleL2) (hv : Measurable v) :
    Measurable (fun z => circleHeatOperator (t z) (ht0 z) (v z)) := by
  have hm : Measurable (fun p : ℝ × CircleL2 => HeatAgeContinuity.heat p.1 p.2) :=
    HeatAgeContinuity.continuous_heat_action.measurable
  have hp : Measurable (fun z => (t z,v z)) := ht.prodMk hv
  convert! hm.comp hp using 1
  funext z
  exact (HeatAgeContinuity.heat_eq (t:=t z) (ht0 z) (v z)).symm

/-- Actual same-Haar signed noise columns, with their true right heat and
native massive negative-output operator retained. -/
def column (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ) (δ : X → ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z)
    (c d : X → CircleHeat.CircleL2) (z : X) (q : FiniteHaar.HaarNode) : CircleL2 :=
  OneInputOperator.besselHalf Λ ρ hΛ hρ
    (integralOperator F z (circleHeatOperator (δ z/2) (div_nonneg (hδ z) (by norm_num))
      (CircleNormalization.push (FiniteHaar.globalHaarColumn q (d z)-FiniteHaar.globalHaarColumn q (c z)))))

theorem column_measurable {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    {Λ ρ : ℝ} (δ : X → ℝ) (hdelt : Measurable δ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z)
    {c d : X → CircleHeat.CircleL2} (hc : Measurable c) (hd : Measurable d)
    (q : FiniteHaar.HaarNode) : Measurable (fun z => column F Λ ρ δ hΛ hρ hδ c d z q) := by
  unfold column
  have hcol := ((FiniteHaar.measurable_globalHaarColumn q).comp hd).sub
    ((FiniteHaar.measurable_globalHaarColumn q).comp hc)
  have hpush : Measurable (fun z => CircleNormalization.push
      (FiniteHaar.globalHaarColumn q (d z)-FiniteHaar.globalHaarColumn q (c z))) :=
    CircleNormalization.push.continuous.measurable.comp hcol
  have hheat := native_heat_measurable (fun z => δ z/2) (hdelt.div_const 2)
    (fun z => div_nonneg (hδ z) (by norm_num)) _ hpush
  have hact : Continuous (fun p : (CircleL2 →L[ℂ] CircleL2) × CircleL2 => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact (OneInputOperator.besselHalf Λ ρ hΛ hρ).continuous.measurable.comp
    (hact.measurable.comp ((integralOperator_measurable_variable hF hb).prodMk hheat))

def columns (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ) (δ : X → ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (z : X) : Space :=
  HilbertColumns.ofSummable (column F Λ ρ δ hΛ hρ hδ (fun x => (c x).1) (fun x => (d x).1) z)
    (SignedKernelEnergy.energy_summable_and_bound hΛ hρ (hδ z) hm (c z) (d z) z).1

theorem columns_apply (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ) (δ : X → ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (z : X) (q : FiniteHaar.HaarNode) :
    columns F Λ ρ δ hΛ hρ hδ m U hm c d z q=
      column F Λ ρ δ hΛ hρ hδ (fun x => (c x).1) (fun x => (d x).1) z q := rfl

/-- Exact Hilbert norm of the genuine infinite stochastic integrand. -/
theorem norm_sq (F : X × (HeatCircle × HeatCircle) → ℂ) (Λ ρ : ℝ) (δ : X → ℝ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z) (m U : ℝ) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (z : X) :
    ‖columns F Λ ρ δ hΛ hρ hδ m U hm c d z‖^2=
      SignedKernelEnergy.energy F Λ ρ (δ z) hΛ hρ (hδ z) (c z).1 (d z).1 z :=
  HilbertColumns.norm_sq _

/-- True Hilbert-valued measurability, hence predictability when X carries
the predictable sigma algebra and the supplied scalar/state data are
measurable for it. No independence is required. -/
theorem columns_measurable {F : X × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    {Λ ρ m U : ℝ} (δ : X → ℝ) (hdelt : Measurable δ)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (hδ : ∀ z, 0 ≤ δ z) (hm : 0 < m)
    (c d : X → FiniteHaar.EllipticField m U) (hc : Measurable c) (hd : Measurable d) :
    Measurable (columns F Λ ρ δ hΛ hρ hδ m U hm c d) := by
  apply HilbertColumns.measurable_of_columns
  intro q
  exact column_measurable hF hb δ hdelt hΛ hρ hδ
    (measurable_subtype_coe.comp hc) (measurable_subtype_coe.comp hd) q

end SHE.SignedKernelColumns
