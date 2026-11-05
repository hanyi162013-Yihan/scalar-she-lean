module

public import SHE.ActualNoiseIntegrand
public import SHE.RawKernelColumns
public import SHE.QuarterKernelTimes

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory AddCircle Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  NormalizedKernelSplit
open scoped ENNReal
local instance actualRawNoise_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance actualRawNoise_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance actualRawNoise_exponentFinite : Fact ((2:ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance actualRawNoise_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualRawNoise_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualRawNoise_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance actualRawNoise_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance actualRawNoise_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance actualRawNoise_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

/-- The raw conditional-mean noise integrand, with the original terminal
q-law, q-current mean and same-Haar factor difference. No extra heat is
inserted in this definition. -/
def controlledRawNoiseColumns (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq0 : ∀ x, 0 ≤ q x) (ell U : ℝ) (hell : 0 < ell) (u d : CircleL2)
    (Z D : X → CircleL2) (θ : X → ℝ) (t : X → Fin k → ℝ)
    (c e : X → FiniteHaar.EllipticField ell U) : X → SignedKernelColumns.Space :=
  SignedKernelColumns.rawColumns (controlledVariableField L k Λ q hq0 u d Z D θ t)
    Λ ρ hΛ hρ ell U hell c e

theorem controlledRawNoiseColumns_measurable (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (q : X → ℝ) (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (ell U : ℝ) (hell : 0 < ell) (u d : CircleL2)
    (Z D : X → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : X → ℝ) (hθ : Measurable θ) (t : X → Fin k → ℝ) (ht : Measurable t)
    (c e : X → FiniteHaar.EllipticField ell U) (hc : Measurable c) (he : Measurable e) :
    Measurable (controlledRawNoiseColumns L k Λ ρ hΛ hρ q hq0 ell U hell u d Z D θ t c e) := by
  apply SignedKernelColumns.rawColumns_measurable
    (controlled_spatial_variable_measurable L k Λ q hq hq0 u d Z D hZ hD θ hθ t ht)
    _ hΛ hρ hell c e hc he
  intro x
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=X) T hT k (q x) (t x)
  exact ⟨B,hB,fun y z => hbound (controlledMean L k Λ (q x) (hq0 x) u d Z D (θ x)) x y z⟩

/-- The raw Hilbert-valued integrand equals the separated quarter-kernel
integrand in every actual Haar coordinate, including inactive times.
This is the exact identity needed before good/bad truncation. -/
theorem rawColumns_eq_quarterColumns (T : ℝ) (hT : ∀ p, L.terminal p=T)
    (k : ℕ) (q : ℝ) (m : X → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : X × History HeatCircle k => m z.1 z.2))
    (t : Fin k → ℝ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (ell U : ℝ) (hell : 0 < ell) (c d : X → FiniteHaar.EllipticField ell U) (x : X) :
    SignedKernelColumns.rawColumns (field L k q m t) Λ ρ hΛ hρ ell U hell c d x=
      SignedKernelColumns.columns
        (rowField L k q (quarterRowTime (R:=R) T k q t) m t)
        Λ ρ (fun _ => quarterTraceTime (R:=R) T k q t) hΛ hρ
        (fun _ => quarterTraceTime_nonneg T k q t) ell U hell c d x := by
  apply lp.ext
  funext i
  rw [SignedKernelColumns.rawColumns_apply,SignedKernelColumns.columns_apply]
  unfold SignedKernelColumns.column
  rw [quarter_operator_split L T hT k q m hm t x]
  rfl

end SHE.ActualMeanKernel
