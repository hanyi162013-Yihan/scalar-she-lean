module

public import SHE.NativeRealNoise

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.NativeRealNoise
open Set MeasureTheory Real StoppedFourier ActualMeanKernel CutoffWordLevel CutoffWordHistories
  PredictableL2
open scoped ENNReal NNReal
local instance realJointNoise_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance realJointNoise_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance realJointNoise_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance realJointNoise_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance realJointNoise_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
local instance realJointNoise_realColumnsMeasurable : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance realJointNoise_realColumnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] {R : ReferenceData} {n : ℕ}

theorem columnsPart_norm_sq_of_fixed (v : SignedKernelColumns.Space)
    (hv : columnsEmbed (columnsPart v)=v) : ‖columnsPart v‖^2=‖v‖^2 := by
  rw [←columnsEmbed_norm_sq (columnsPart v),hv]

/-- The real-column identification also commutes with the actual old
parameter average. Off the Bochner-integrable branch both averages are
zero; on its true branch the identity follows from bounded linearity. -/
theorem columns_integral_fixed (ν : Measure A) (F : A → SignedKernelColumns.Space)
    (hF : ∀ a,columnsEmbed (columnsPart (F a))=F a) :
    columnsEmbed (columnsPart (∫ a,F a ∂ν))=∫ a,F a ∂ν := by
  by_cases hi : Integrable F ν
  · rw [←columnsPart.integral_comp_comm hi,
      ←columnsEmbed.integral_comp_comm (columnsPart.integrable_comp hi)]
    exact integral_congr_ae (ae_of_all _ hF)
  · rw [integral_undef hi,map_zero,map_zero]

theorem oldTimeJointNoise_fixed (L : CutoffWordLevel.Level R HeatCircle n)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) (ht : Measurable t)
    (U V : ℝ≥0 × Ω → CircleL2) (hU : Measurable U) (hV : Measurable V)
    (ell M : ℝ) (hell : 0 < ell) (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (z : A × (ℝ≥0 × Ω)) :
    columnsEmbed (columnsPart (oldTimeJointNoise L k Λ ρ hΛ hρ t U V ell M hell c d z))=
      oldTimeJointNoise L k Λ ρ hΛ hρ t U V ell M hell c d z := by
  let F := jointVariableField L k Λ (fun z : A × (ℝ≥0 × Ω) => (z.2.1:ℝ))
    (fun z => U z.2) (fun z => V z.2) (fun z => t z.1)
  have hF : Measurable F := jointVariableField_measurable L k Λ _
    (measurable_subtype_coe.comp measurable_snd.fst) _ _
    (hU.comp measurable_snd) (hV.comp measurable_snd) _ (ht.comp measurable_fst)
  have hb : ∀ z,∃ B : ℝ,0 ≤ B ∧ ∀ y x,‖F (z,(y,x))‖ ≤ B := by
    intro z
    obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=A × (ℝ≥0 × Ω)) T hT k (z.2.1:ℝ) (t z.1)
    exact ⟨B,hB,fun y x => hbound (currentJointMean L k Λ _ _ _) z y x⟩
  have hr (z) (y x : HeatCircle) : (F (z,(y,x))).im=0 := Complex.ofReal_im _
  exact rawColumns_embed hF hb hr hΛ hρ hell (fun z => c z.2) (fun z => d z.2) z

/-- The averaged real integrand has exactly the expected complex trace
norm, in the original unit-circle real Itô column space. -/
theorem averagedJointNoise_norm_sq (L : CutoffWordLevel.Level R HeatCircle n)
    (ν : Measure A) (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) (ht : Measurable t)
    (U V : ℝ≥0 × Ω → CircleL2) (hU : Measurable U) (hV : Measurable V)
    (ell M : ℝ) (hell : 0 < ell) (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (z : ℝ≥0 × Ω) :
    ‖columnsPart (averagedJointNoise L ν k Λ ρ hΛ hρ t U V ell M hell c d z)‖^2=
      ‖averagedJointNoise L ν k Λ ρ hΛ hρ t U V ell M hell c d z‖^2 :=
  columnsPart_norm_sq_of_fixed _ (columns_integral_fixed ν _
    (fun a => oldTimeJointNoise_fixed L T hT k Λ ρ hΛ hρ t ht U V hU hV ell M hell c d (a,z)))

end SHE.NativeRealNoise
