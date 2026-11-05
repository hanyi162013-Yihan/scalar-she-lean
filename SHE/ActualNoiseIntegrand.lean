module

public import SHE.ActualMeanOperator
public import SHE.SignedKernelColumns

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  NormalizedKernelSplit
open scoped ENNReal
local instance actualNoiseIntegrand_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance actualNoiseIntegrand_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance actualNoiseIntegrand_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance actualNoiseIntegrand_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualNoiseIntegrand_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualNoiseIntegrand_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance actualNoiseIntegrand_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance actualNoiseIntegrand_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance actualNoiseIntegrand_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

/-- The displayed right-heated physical-kernel integrand. Both coefficient
fields use the same countable Haar coordinates. Identifying this with the
raw terminal noise row requires the separate row-time factorization; the
definition itself does not assert that identification. -/
def controlledNoiseColumns (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq0 : ∀ x, 0 ≤ q x) (δ : X → ℝ) (hδ : ∀ x, 0 ≤ δ x)
    (ell U : ℝ) (hell : 0 < ell) (u d : CircleL2)
    (Z D : X → CircleL2) (θ : X → ℝ) (t : X → Fin k → ℝ)
    (c e : X → FiniteHaar.EllipticField ell U) : X → SignedKernelColumns.Space :=
  SignedKernelColumns.columns (controlledVariableField L k Λ q hq0 u d Z D θ t)
    Λ ρ δ hΛ hρ hδ ell U hell c e

/-- All countably many actual columns form a genuine Hilbert-valued
measurable integrand. Taking X with its predictable sigma algebra gives
predictability from the actual predictable current states/coefficient
fields and measurable time data, with no separate kernel hypothesis. -/
theorem controlledNoiseColumns_measurable (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (δ : X → ℝ) (hδM : Measurable δ) (hδ : ∀ x, 0 ≤ δ x)
    (ell U : ℝ) (hell : 0 < ell) (u d : CircleL2)
    (Z D : X → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) (t : X → Fin k → ℝ) (ht : Measurable t)
    (c e : X → FiniteHaar.EllipticField ell U) (hc : Measurable c) (he : Measurable e) :
    Measurable (controlledNoiseColumns L k Λ ρ hΛ hρ q hq0 δ hδ ell U hell u d Z D θ t c e) := by
  apply SignedKernelColumns.columns_measurable
    (controlled_spatial_variable_measurable L k Λ q hq hq0 u d Z D hZ hD θ hθ t ht)
    _ δ hδM hΛ hρ hδ hell c e hc he
  intro x
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=X) T hT k (q x) (t x)
  exact ⟨B,hB,fun y z => hbound (controlledMean L k Λ (q x) (hq0 x) u d Z D (θ x)) x y z⟩

/-- Its true Hilbert norm is exactly the actual signed trace entering the
normalized-kernel estimate and later stochastic isometry. -/
theorem controlledNoiseColumns_norm_sq (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq0 : ∀ x, 0 ≤ q x) (δ : X → ℝ) (hδ : ∀ x, 0 ≤ δ x)
    (ell U : ℝ) (hell : 0 < ell) (u d : CircleL2)
    (Z D : X → CircleL2) (θ : X → ℝ) (t : X → Fin k → ℝ)
    (c e : X → FiniteHaar.EllipticField ell U) (x : X) :
    ‖controlledNoiseColumns L k Λ ρ hΛ hρ q hq0 δ hδ ell U hell u d Z D θ t c e x‖^2=
      SignedKernelEnergy.energy (controlledVariableField L k Λ q hq0 u d Z D θ t)
        Λ ρ (δ x) hΛ hρ (hδ x) (c x).1 (e x).1 x :=
  SignedKernelColumns.norm_sq (controlledVariableField L k Λ q hq0 u d Z D θ t)
    Λ ρ δ hΛ hρ hδ ell U hell c e x

end SHE.ActualMeanKernel
