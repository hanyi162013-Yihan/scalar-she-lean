module
public import SHE.NativeStoppedNoiseIncrement
public import SHE.NativeVolterraExpectedSection
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeStoppedEnergy
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
local notation "Eγ" => NativeWeightedProcess.energy 𝓕 μ H

include hrep in
theorem raw_energy (γ : ℝ) :
    (∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖D t ω‖^2) ∂μ ∂timeMeasure H) = Eγ γ d := by
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod hrep] with t ht
  apply lintegral_congr_ae
  filter_upwards [ht] with ω hω
  change D t ω = d (t,ω) at hω
  rw [hω]

include hLip hD hrep in
/-- The actual stopped difference inequality, ordinary Ito isometry and
native heat estimates give a strict weighted-energy contraction. -/
theorem estimate {γ : ℝ} (hγ : 0 < γ)
    (hmem : ∀ω, MemLp (fun s : ℝ≥0 => Real.exp (-γ*(s:ℝ)) • D s ω) 2 (timeMeasure H))
    (hbound : ∀ᵐt∂timeMeasure H, ∀ᵐω∂μ,
      ‖D t ω‖^2 ≤ 2*Λ^2*‖NativeClock.volterra Λ (fun s => D s ω) t‖^2 + 2*‖N t ω‖^2) :
    Eγ γ d ≤ ENNReal.ofReal
      (Λ^2*(H:ℝ)/(Λ+γ) + 2*NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ) * Eγ γ d := by
  let c : ℝ := 1/(2*(Λ+γ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : 0 ≤ 2*Λ^2 := by positivity
  have hC : 0 ≤ NativeBieleckiColumnEnergy.constant ell M L := NativeBieleckiColumnEnergy.constant_nonneg hM L
  have hB : 0 ≤ BieleckiKernel.mass γ := BieleckiKernel.mass_nonneg hγ.le
  have hi (t : ℝ≥0) (ht : t ≤ H)
      (hbnd : ∀ᵐω∂μ, ‖D t ω‖^2 ≤ 2*Λ^2*‖NativeClock.volterra Λ (fun s => D s ω) t‖^2 + 2*‖N t ω‖^2) :
      (∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖D t ω‖^2) ∂μ) ≤
        (ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal c)*Eγ γ d +
          ENNReal.ofReal 2*(∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖N t ω‖^2) ∂μ) := by
    let V : Ω → ℝ := fun ω => Real.exp (-2*γ*(t:ℝ))*‖NativeClock.volterra Λ (fun s => D s ω) t‖^2
    let Z : Ω → ℝ := fun ω => Real.exp (-2*γ*(t:ℝ))*‖N t ω‖^2
    have hV : Measurable V := measurable_const.mul ((NativeVolterraFields.measurable Λ D hD t).norm.pow_const 2)
    have hV0 : ∀ω, 0 ≤ V ω := fun ω => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have hZ0 : ∀ω, 0 ≤ Z ω := fun ω => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have hvb : (∫⁻ω, ENNReal.ofReal (V ω) ∂μ) ≤ ENNReal.ofReal c*Eγ γ d := by
      have hh := NativeVolterraExpectedSection.bound μ H hΛ hγ D hD hmem t ht
      rw [raw_energy 𝓕 μ H d D hrep γ] at hh
      exact hh
    calc
      _ ≤ ∫⁻ω, ENNReal.ofReal ((2*Λ^2)*V ω+2*Z ω) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hbnd] with ω hω
        apply ENNReal.ofReal_le_ofReal
        have hh := mul_le_mul_of_nonneg_left hω (Real.exp_pos (-2*γ*(t:ℝ))).le
        convert hh using 1 <;> dsimp [V,Z] <;> ring
      _ = ENNReal.ofReal (2*Λ^2)*(∫⁻ω, ENNReal.ofReal (V ω) ∂μ) +
          ENNReal.ofReal 2*(∫⁻ω, ENNReal.ofReal (Z ω) ∂μ) := by
        have hsplit (ω : Ω) : ENNReal.ofReal ((2*Λ^2)*V ω+2*Z ω) =
            ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal (V ω)+ENNReal.ofReal 2*ENNReal.ofReal (Z ω) := by
          exact (ENNReal.ofReal_add (mul_nonneg hA (hV0 ω)) (mul_nonneg (by norm_num) (hZ0 ω))).trans
            (congrArg₂ (fun x y : ℝ≥0∞ => x+y) (ENNReal.ofReal_mul hA)
              (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)))
        simp_rw [hsplit]
        have hleft : Measurable (fun ω : Ω => ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal (V ω)) :=
          measurable_const.mul (ENNReal.continuous_ofReal.measurable.comp hV)
        rw [lintegral_add_left hleft]
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
        simpa only [mul_assoc,Z] using add_le_add (mul_le_mul_right hvb (ENNReal.ofReal (2*Λ^2))) (le_refl (ENNReal.ofReal 2*(∫⁻ω, ENNReal.ofReal (Z ω) ∂μ)))
  have hnoise := NativeStoppedNoiseIncrement.energy 𝓕 μ H hH hΛ hell hM I ha hb hcoef W hW d hLip hγ
  calc
    Eγ γ d = ∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖D t ω‖^2) ∂μ ∂timeMeasure H :=
      (raw_energy 𝓕 μ H d D hrep γ).symm
    _ ≤ ∫⁻t, (ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal c)*Eγ γ d +
        ENNReal.ofReal 2*(∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖N t ω‖^2) ∂μ) ∂timeMeasure H := by
      apply lintegral_mono_ae
      filter_upwards [timeMeasure_ae_mem H,hbound] with t ht hbnd
      exact hi t ht.2 hbnd
    _ = (ENNReal.ofReal (H:ℝ)*ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal c)*Eγ γ d +
        ENNReal.ofReal 2*(∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖N t ω‖^2) ∂μ ∂timeMeasure H) := by
      rw [lintegral_add_left measurable_const]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [lintegral_const,timeMeasure_mass]
      ring
    _ ≤ _ := by
      apply le_trans (add_le_add (le_refl _) (mul_le_mul_right hnoise (ENNReal.ofReal 2)))
      have he : (H:ℝ)*(2*Λ^2)*c + 2*(NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ) =
          Λ^2*(H:ℝ)/(Λ+γ)+2*NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ := by
        dsimp [c]
        field_simp [show Λ+γ ≠ 0 by linarith]
        <;> ring
      have hcoefEq : ENNReal.ofReal (H:ℝ)*ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal c +
          ENNReal.ofReal 2*ENNReal.ofReal (NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ) =
          ENNReal.ofReal (Λ^2*(H:ℝ)/(Λ+γ)+2*NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ) := by
        have hfirst : ENNReal.ofReal (H:ℝ)*ENNReal.ofReal (2*Λ^2)*ENNReal.ofReal c =
            ENNReal.ofReal ((H:ℝ)*(2*Λ^2)*c) :=
          (congrArg (fun z : ℝ≥0∞ => z*ENNReal.ofReal c) (ENNReal.ofReal_mul H.2).symm).trans
            (ENNReal.ofReal_mul (mul_nonneg H.2 hA)).symm
        have hsecond : ENNReal.ofReal 2*ENNReal.ofReal (NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ) =
            ENNReal.ofReal (2*(NativeBieleckiColumnEnergy.constant ell M L*BieleckiKernel.mass γ)) :=
          (ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)).symm
        exact (congrArg₂ (fun x y : ℝ≥0∞ => x+y) hfirst hsecond).trans
          ((ENNReal.ofReal_add (mul_nonneg (mul_nonneg H.2 hA) hc)
            (mul_nonneg (by norm_num) (mul_nonneg hC hB))).symm.trans (congrArg ENNReal.ofReal he))
      simpa only [add_mul,mul_assoc] using le_of_eq (congrArg (fun z : ℝ≥0∞ => z*Eγ γ d) hcoefEq)
end SHE.NativeStoppedEnergy
