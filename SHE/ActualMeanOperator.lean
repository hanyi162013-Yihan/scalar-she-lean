module

public import SHE.ActualControlledKernelJoint
public import SHE.NativeKernelVariable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  NormalizedKernelSplit
open scoped ENNReal
local instance actualMeanOperator_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance actualMeanOperator_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance actualMeanOperator_exponentLower : Fact (1 ≤ (2:ℝ≥0∞)) := ⟨by norm_num⟩
local instance actualMeanOperator_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualMeanOperator_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualMeanOperator_kernelSecondCountable : SecondCountableTopology NativeRandomKernel.KernelSpace := Lp.SecondCountableTopology
local instance actualMeanOperator_kernelMeasurable : MeasurableSpace NativeRandomKernel.KernelSpace := borel NativeRandomKernel.KernelSpace
local instance actualMeanOperator_kernelBorel : BorelSpace NativeRandomKernel.KernelSpace := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

def variableField (k : ℕ) (q : X → ℝ)
    (m : X → History HeatCircle k → WordRecursion.State (n+k)) (t : X → Fin k → ℝ) : X × Space → ℂ :=
  fun z => spatial L k (q z.1) m (t z.1) z.1 z.2.1 z.2.2

theorem variableField_measurable (k : ℕ) (q : X → ℝ) (hq : Measurable q)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) : Measurable (variableField L k q m t) :=
  spatial_variable_measurable L k q hq m hm t ht

theorem variableField_section_bound (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : X → ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (t : X → Fin k → ℝ) (z : X) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y x, ‖variableField L k q m t (z,(y,x))‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=X) T hT k (q z) (t z)
  exact ⟨B,hB,fun y x => hbound m z y x⟩

/-- The actual unsmoothed physical word kernel is a jointly measurable
Hilbert-valued kernel, with no uniform coarse bound near time diagonals. -/
theorem variableKernel_measurable (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : X → ℝ) (hq : Measurable q)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (NativeRandomKernel.kernel (variableField L k q m t)) :=
  NativeRandomKernel.kernel_measurable_variable (variableField_measurable L k q hq m hm t ht)
    (variableField_section_bound L T hT k q m t)

theorem variableOperator_measurable (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : X → ℝ) (hq : Measurable q)
    (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (NativeRandomKernel.integralOperator (variableField L k q m t)) :=
  NativeRandomKernel.integralOperator_measurable_variable (variableField_measurable L k q hq m hm t ht)
    (variableField_section_bound L T hT k q m t)

def controlledVariableField (k : ℕ) (Λ : ℝ) (q : X → ℝ) (hq0 : ∀ x, 0 ≤ q x)
    (u d : CircleL2) (Z D : X → CircleL2) (θ : X → ℝ) (t : X → Fin k → ℝ) : X × Space → ℂ :=
  fun z => spatial L k (q z.1) (controlledMean L k Λ (q z.1) (hq0 z.1) u d Z D (θ z.1))
    (t z.1) z.1 z.2.1 z.2.2

/-- The literal compensated future-mean spatial operator is measurable
in operator norm over the original parameter sigma algebra. Hence it is
predictable whenever the supplied process data are predictable. -/
theorem controlledOperator_measurable (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (Λ : ℝ) (q : X → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (u d : CircleL2) (Z D : X → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) (t : X → Fin k → ℝ) (ht : Measurable t) :
    Measurable (NativeRandomKernel.integralOperator (controlledVariableField L k Λ q hq0 u d Z D θ t)) := by
  apply NativeRandomKernel.integralOperator_measurable_variable
    (controlled_spatial_variable_measurable L k Λ q hq hq0 u d Z D hZ hD θ hθ t ht)
  intro z
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=X) T hT k (q z) (t z)
  exact ⟨B,hB,fun y x => hbound (controlledMean L k Λ (q z) (hq0 z) u d Z D (θ z)) z y x⟩

end SHE.ActualMeanKernel
