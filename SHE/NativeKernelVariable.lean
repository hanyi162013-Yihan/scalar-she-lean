module

public import SHE.NativeRandomKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRandomKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier
open scoped ENNReal
local instance nativeKernelVariable_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance nativeKernelVariable_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeKernelVariable_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance nativeKernelVariable_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance nativeKernelVariable_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance nativeKernelVariable_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeKernelVariable_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance nativeKernelVariable_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeKernelVariable_kernelSecondCountable : SecondCountableTopology KernelSpace := Lp.SecondCountableTopology
local instance nativeKernelVariable_kernelMeasurable : MeasurableSpace KernelSpace := borel KernelSpace
local instance nativeKernelVariable_kernelBorel : BorelSpace KernelSpace := ⟨rfl⟩
variable {X : Type*} [MeasurableSpace X]
variable {F : X × (HeatCircle × HeatCircle) → ℂ}

private theorem unit_column_sections (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    (z : X × HeatCircle) :
    MemLp (fun x => NativeRandomRows.unitField (columnField F) (z,x)) 2
      (haarAddCircle (T:=(1:ℝ))) := by
  obtain ⟨B,_,hB⟩ := hb z.1
  exact MemLp.of_bound
    (((NativeRandomRows.unitField_measurable (columnField_measurable hF)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable) B
    (ae_of_all _ (fun x => hB z.2 _))

/-- Actual L² column measurability needs only a finite bound on each
parameter section. No bound uniform over terminal times is required. -/
theorem column_measurable_variable (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B) :
    Measurable (column F) := by
  exact CircleNormalization.push.continuous.measurable.comp
    (MeasurableL2Field.realizeL2_measurable
      (NativeRandomRows.unitField_measurable (columnField_measurable hF)) (unit_column_sections hF hb))

theorem column_ae_variable (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    (z : X) (y : HeatCircle) : (column F (z,y) : HeatCircle → ℂ)=ᵐ[haarAddCircle]
      fun x => F (z,(y,x)) := by
  have hu := MeasurableL2Field.realizeL2_ae _ (unit_column_sections hF hb) (z,y)
  have hp := (CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae hu
  filter_upwards [CircleNormalization.push_ae
    (RandomRowEnergy.row (NativeRandomRows.unitField (columnField F)) (z,y)),hp] with x hx hy
  change RandomRowEnergy.row (NativeRandomRows.unitField (columnField F)) (z,y)
    (CircleNormalization.scale (2*π) 1 x)=_ at hy
  change CircleNormalization.push (RandomRowEnergy.row (NativeRandomRows.unitField (columnField F)) (z,y)) x=F (z,(y,x))
  rw [hx,hy]
  change F (z,(y,CircleNormalization.scale 1 (2*π) (NativeHeatSpan.unitCenter x)))=F (z,(y,x))
  rw [NativeHeatSpan.scale_inverse]

theorem column_norm_le_section (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    (z : X) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y x, ‖F (z,(y,x))‖ ≤ B)
    (y : HeatCircle) : ‖column F (z,y)‖ ≤ B := by
  have hh := Lp.norm_le_of_ae_bound hB ((column_ae_variable hF hb z y).mono (fun x hx => by
    change column F (z,y) x=F (z,(y,x)) at hx
    rw [hx]
    exact hbound y x))
  simpa [measureUnivNNReal] using hh

theorem column_memLp_variable (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B) (z : X) :
    MemLp (fun y => column F (z,y)) 2 haarAddCircle := by
  obtain ⟨B,hB,hbound⟩ := hb z
  exact MemLp.of_bound ((column_measurable_variable hF hb).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (ae_of_all _ (fun y => column_norm_le_section hF hb z hB hbound y))

/-- The actual Hilbert-valued integral kernel is jointly Borel under
sectionwise finite coarse bounds, even as those bounds diverge near time
diagonals. -/
theorem kernel_measurable_variable (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B) :
    Measurable (kernel F) :=
  HilbertL2Fields.realize_measurable (column_measurable_variable hF hb) (column_memLp_variable hF hb)

/-- The genuine spatial integral operator, rather than a family of scalar
versions, is measurable in operator norm over the parameter sigma algebra. -/
theorem integralOperator_measurable_variable (hF : Measurable F)
    (hb : ∀ z, ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖F (z,(y,x))‖ ≤ B) :
    Measurable (integralOperator F) :=
  KernelOperator.synthesis_continuous.measurable.comp (kernel_measurable_variable hF hb)

end SHE.NativeRandomKernel
