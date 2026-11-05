module
public import SHE.NativeStoppedEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeStoppedEnergyZero
open MeasureTheory Set PredictableL2 FiniteHaar LowBands
open scoped NNReal ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2 :=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace StateL2 := borel _
local instance : BorelSpace StateL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
local instance (ell M : ℝ) : MeasurableSpace (EllipticField ell M) := borel _
local instance (ell M : ℝ) : BorelSpace (EllipticField ell M) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H : ℝ≥0) (hH : (H:ℝ) ≤ 1) {Λ ell M : ℝ}
variable (hΛ : 0 ≤ Λ) (hell : 0 < ell) (hM : 0 ≤ M)
variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=StateL2) 𝓕 μ H)
variable {a : ℝ → ℝ} (ha : Measurable a) (hb : ∀z, ell ≤ a z ∧ a z ≤ M)
variable (hcoef : Measurable (NonlinearHaarIntegrand.coefficientField a ha ell M hell hb))
variable {L : ℝ≥0} (hLip : LipschitzWith L (fun z => (a z:ℂ)))
variable (W : ℝ≥0 × Ω → StateL2) (hW : StronglyMeasurable[𝓕.predictable] W)
variable (d : Process (E:=StateL2) 𝓕 μ H)
variable (D : ℝ≥0 → Ω → StateL2) (hD : Measurable (Function.uncurry D))
variable (hrep : Function.uncurry D =ᵐ[energyMeasure μ H] d)
local notation "N" => NativeStoppedNoiseIncrement.noise 𝓕 μ H hH hΛ hell hM I ha hb hcoef W hW d

include hLip hD hrep in
/-- An actual stopped difference satisfying the derived native mild
norm inequality vanishes, on the full prescribed comparison interval.
Neither a small Lipschitz-dependent horizon nor a contraction premise
is supplied. The weight and its quantitative contraction are proved. -/
theorem eq_zero
    (hmem : ∀ω, MemLp (fun s : ℝ≥0 => D s ω) 2 (timeMeasure H))
    (hbound : ∀ᵐt∂timeMeasure H, ∀ᵐω∂μ,
      ‖D t ω‖^2 ≤ 2*Λ^2*‖NativeClock.volterra Λ (fun s => D s ω) t‖^2 + 2*‖N t ω‖^2) :
    d = 0 := by
  let C : ℝ := NativeBieleckiColumnEnergy.constant ell M L
  obtain ⟨γ,hγ1,hsmall⟩ := NativeWeightedVolterraEnergy.exists_weight (Λ^2*(H:ℝ)) (2*C)
  have hγ : 0 < γ := by linarith
  have hmemγ (ω : Ω) : MemLp (fun s : ℝ≥0 => Real.exp (-γ*(s:ℝ)) • D s ω) 2 (timeMeasure H) := by
    have hDm : Measurable (fun s : ℝ≥0 => D s ω) := hD.comp (measurable_id.prodMk measurable_const)
    have he : Measurable (fun s : ℝ≥0 => Real.exp (-γ*(s:ℝ))) :=
      (measurable_coe_nnreal_real.const_mul (-γ)).exp
    apply (hmem ω).of_le (he.smul hDm).stronglyMeasurable.aestronglyMeasurable
    apply ae_of_all
    intro s
    change ‖Real.exp (-γ*(s:ℝ)) • D s ω‖ ≤ ‖D s ω‖
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hExp : Real.exp (-γ*(s:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [s.2])
    exact mul_le_of_le_one_left (norm_nonneg _) hExp
  have hest := NativeStoppedEnergy.estimate 𝓕 μ H hH hΛ hell hM I ha hb hcoef hLip W hW d D hD hrep hγ hmemγ hbound
  let q : ℝ := Λ^2*(H:ℝ)/(Λ+γ)+2*C*BieleckiKernel.mass γ
  have hC : 0 ≤ C := NativeBieleckiColumnEnergy.constant_nonneg hM L
  have hmass : 0 ≤ BieleckiKernel.mass γ := BieleckiKernel.mass_nonneg hγ.le
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hfrac : Λ^2*(H:ℝ)/(Λ+γ) ≤ Λ^2*(H:ℝ)/γ :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) H.2) hγ (by linarith)
  have hq : q ≤ 1/8 := by dsimp [q]; linarith only [hsmall,hfrac]
  exact NativeWeightedProcess.eq_zero_of_contract 𝓕 μ H γ d hq0
    (lt_of_le_of_lt hq (by norm_num)) hest
end SHE.NativeStoppedEnergyZero
