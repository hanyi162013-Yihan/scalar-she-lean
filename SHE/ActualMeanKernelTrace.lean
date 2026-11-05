module

public import SHE.ActualMeanKernelBounds
public import SHE.RelativeKernelTruncationZero

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set Filter MeasureTheory AddCircle Real StoppedFourier CutoffWordLevel CutoffWordHistories
  NormalizedKernelSplit NativeSignedHaarProcess SignedKernelTruncation
local instance actualMeanKernelTrace_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩
local instance actualMeanKernelTrace_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance actualMeanKernelTrace_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance actualMeanKernelTrace_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance actualMeanKernelTrace_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualMeanKernelTrace_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

/-- The literal spatially averaged physical derivative, with the input
point first and the scalar output/root point second. -/
def field (k : ℕ) (q : ℝ) (m : Ω → History HeatCircle k → WordRecursion.State (n+k))
    (t : Fin k → ℝ) : Ω × Space → ℂ :=
  fun z => spatial L k q m t z.1 z.2.1 z.2.2

theorem field_measurable (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (n+k))
    (hm : Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2)) (t : Fin k → ℝ) :
    Measurable (field L k q m t) := spatial_measurable L k q m hm t

theorem field_real (k : ℕ) (q : ℝ)
    (m : Ω → History HeatCircle k → WordRecursion.State (n+k)) (t : Fin k → ℝ)
    (z : Ω × Space) : (field L k q m t z).im=0 := by
  exact Complex.ofReal_im _

/-- The genuine compensated future-mean substitution, retaining all
original target times and physical centers. -/
def controlledField (k : ℕ) (Λ q : ℝ) (hq : 0 ≤ q)
    (u d : CircleL2) (Z D : Ω → CircleL2) (θ : ℝ) (t : Fin k → ℝ) : Ω × Space → ℂ :=
  field L k q (controlledMean L k Λ q hq u d Z D θ) t

theorem controlledField_measurable (k : ℕ) (Λ q : ℝ) (hq : 0 ≤ q)
    (u d : CircleL2) (Z D : Ω → CircleL2) (hZ : Measurable Z) (hD : Measurable D)
    (θ : ℝ) (t : Fin k → ℝ) : Measurable (controlledField L k Λ q hq u d Z D θ t) :=
  field_measurable L k q _ (controlledMean_measurable L k Λ q hq u d Z D hZ hD θ) t

/-- This applies the actual good/bad operator truncation to the actual
physical word. Borel dependence, reality, coarse Fubini bounds and
column-energy integrability are derived. The only sharp input here is
the displayed relative moment estimate, to be supplied by the actual
Gaussian score and heat-forest calculation. -/
theorem exists_spatial_signed_truncation
    (ell U : ℝ) (hell : 0 < ell) {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    ∃ J : ℝ, 0 < J ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (T : ℝ), (∀ p, L.terminal p=T) → ∀ (k : ℕ) (q : ℝ)
      (m : Ω → History HeatCircle k → WordRecursion.State (n+k)),
      Measurable (fun z : Ω × History HeatCircle k => m z.1 z.2) →
      ∀ (t : Fin k → ℝ) (Λ δ w D lam ε P C : ℝ)
      (hΛ : 1 ≤ Λ) (hδ : 0 < δ) (hw : 0 < w),
      w ≤ 1 → δ ≤ w → 0 ≤ D → 1 ≤ lam → 0 ≤ C →
      ∀ (r : ℕ), P ≤ ε*(2*r) →
      (∀ᵐ p : Space ∂(haarAddCircle (T:=2*π)).prod haarAddCircle,
        (∫ ω, ‖field L k q m t (ω,p)‖^(2*r+2) ∂μ) ≤ C*(heatEnvelope D δ w p)^(2*r+2)) →
      ∀ (c d : Ω → FiniteHaar.EllipticField ell U), Measurable c → Measurable d →
      Integrable (fun ω => SignedKernelEnergy.energy (field L k q m t)
        Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω) μ ∧
      (∫ ω, SignedKernelEnergy.energy (field L k q m t)
        Λ ρ δ hΛ hρ.le hδ.le (c ω).1 (d ω).1 ω ∂μ) ≤
        2*goodCost J ρ δ w (lam^ε) (heatAmplitude D δ w)*
          (∫ ω, inputEnergy hΛ hρ.le (c ω) (d ω) ∂μ)+
          8*U*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-P) := by
  obtain ⟨J,hJ,htrace⟩ := exists_expected_relative_nonnegative (Ω:=Ω) ell U hell hρ hρhalf
  refine ⟨J,hJ,?_⟩
  intro μ _ T hT k q m hm t Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD hlam hC r hExponent hbound c d hc hd
  obtain ⟨B,hB,hcoarse⟩ := spatial_uniform_bound L (Ω:=Ω) T hT k q t
  have hFn (p : Space) : Integrable (fun ω => ‖field L k q m t (ω,p)‖^(2*r+2)) μ := by
    have hmeas : Measurable (fun ω => ‖field L k q m t (ω,p)‖^(2*r+2)) :=
      (((field_measurable L k q m hm t).comp (measurable_id.prodMk measurable_const)).norm).pow_const _
    exact (integrable_const (B^(2*r+2))).mono' hmeas.aestronglyMeasurable
      (ae_of_all μ (fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoarse m ω p.1 p.2) _))
  exact htrace μ Λ δ w D lam ε P C hΛ hδ hw hw1 hδw hD hlam hC r hExponent
    (field L k q m t) (field_measurable L k q m hm t) (field_real L k q m t)
    B hB (fun ω y x => hcoarse m ω y x) (ae_of_all _ hFn) hbound c d hc hd

end SHE.ActualMeanKernel
