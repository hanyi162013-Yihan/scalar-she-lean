module

public import SHEStochastic.ScalarLipschitzRawBounds
public import SHEStochastic.ScalarLipschitzContinuousVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzTimeMoments
open MeasureTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzKernelBounds ScalarLipschitzConvolution ScalarLipschitzItoMoment ScalarLipschitzRawBounds
open scoped NNReal ENNReal Topology

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I] [DecidableEq I]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise) (P : FiniteScalarIto.Family F μ H I)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))
  (M : ℝ) (hM₀ : 0≤M)
  (hM : ∀ᵐ s ∂PredictableL2.timeMeasure H,(∫⁻ ω,(coeffSquare hg U (s,ω))^8 ∂μ)≤ENNReal.ofReal M)

include hM in
def value (t : ℝ≥0) (ht : t≤H) : Lp RealL2 2 μ :=
  (ito e P).integral (input e hg U hU t (raw_integrable e hg U hU ENNReal.ofReal_ne_top hM t ht))

include hM in
theorem value_adapted (hn : NullCompleteFiltration.ContainsNullSets F μ) (t : ℝ≥0) (ht : t≤H) :
    StronglyMeasurable[F t] (value e P hg U hU M hM t ht : Ω → RealL2) :=
  adapted e hg U hU P hn t _

set_option linter.unusedSectionVars false in
include hM hM₀ in
theorem increment (s t : ℝ≥0) (hst : s≤t) (ht : t≤H) :
    moment 16 (fun ω => value e P hg U hU M hM t ht ω-value e P hg U hU M hM s (hst.trans ht) ω) μ≤
      ENNReal.ofReal ((NativeScalarBDG.constant 3 : ℝ)*(6*heatConstant (H : ℝ)*(H : ℝ)^(1/4 : ℝ))^8*
        M*((t : ℝ)-(s : ℝ))^2) := by
  let K := heatConstant (H : ℝ)
  let a := input e hg U hU t (raw_integrable e hg U hU ENNReal.ofReal_ne_top hM t ht)
  let b := input e hg U hU s (raw_integrable e hg U hU ENNReal.ofReal_ne_top hM s (hst.trans ht))
  have hd : ∀ᵐ p ∂energyMeasure μ H,ENNReal.ofReal (‖(a-b) p‖^2)≤
      ScalarLipschitzAgeDensity.density K s t p.1*coeffSquare hg U p := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub a b),input_ae e hg U hU t _,
      input_ae e hg U hU s _] with p hab ha hb
    rw [hab,Pi.sub_apply]
    change ENNReal.ofReal (‖a p-b p‖^2)≤_
    rw [ha,hb]
    exact increment_envelope e hg U hst ht p
  have hB := moment_of_density (ito e P) _ (by intro u; exact bdg e P u) (a-b)
    (ScalarLipschitzAgeDensity.density K s t) (ScalarLipschitzAgeDensity.measurable K s t)
    (coeffSquare hg U) (coeffSquare_measurable hg U hU) (ENNReal.ofReal M) hM hd
  have hAE : (ito e P).integral (a-b) =ᵐ[μ] fun ω =>
      value e P hg U hU M hM t ht ω-value e P hg U hU M hM s (hst.trans ht) ω := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  rw [←moment_congr hAE]
  refine hB.trans ?_
  have hmass := ScalarLipschitzAgeDensity.mass (heatConstant_nonneg H.property) hst ht
  have hδ : 0≤(t : ℝ)-(s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
  refine (mul_le_mul_left (mul_le_mul_right (pow_le_pow_left' hmass 8) _) (ENNReal.ofReal M)).trans_eq ?_
  have hK : 0≤heatConstant (H : ℝ) := heatConstant_nonneg H.property
  have hn : 0≤6*heatConstant (H : ℝ)*(H : ℝ)^(1/4 : ℝ)*((t : ℝ)-(s : ℝ))^(1/4 : ℝ) := by
    positivity
  let L : ℝ := 6*heatConstant (H : ℝ)*(H : ℝ)^(1/4 : ℝ)
  let d : ℝ := (t : ℝ)-(s : ℝ)
  let B : ℝ≥0 := NativeScalarBDG.constant 3
  change (B : ℝ≥0∞)*ENNReal.ofReal (L*d^(1/4 : ℝ))^8*ENNReal.ofReal M =
    ENNReal.ofReal ((B : ℝ)*L^8*M*d^2)
  calc
    _ = ENNReal.ofReal ((B : ℝ)*(L*d^(1/4 : ℝ))^8*M) := by
      have he : (B : ℝ≥0∞)=ENNReal.ofReal (B : ℝ) := (ENNReal.ofReal_coe_nnreal (p := B)).symm
      rw [←ENNReal.ofReal_pow (n := 8) (show 0≤L*d^(1/4 : ℝ) from hn),he]
      have h₁ : 0≤(B : ℝ) := B.property
      have h₂ : 0≤(B : ℝ)*(L*d^(1/4 : ℝ))^8 := mul_nonneg h₁ (pow_nonneg hn _)
      rw [←ENNReal.ofReal_mul (q := (L*d^(1/4 : ℝ))^8) h₁,
        ←ENNReal.ofReal_mul (q := M) h₂]
    _ = _ := by
      congr 1
      rw [mul_pow,←Real.rpow_mul_natCast (show 0≤d from hδ)]
      norm_num only [Nat.cast_ofNat,show (1/4 : ℝ)*8=2 by norm_num,Real.rpow_two]
      ring

include hM hM₀ in
theorem exists_version (hH : 0<H) (hn : NullCompleteFiltration.ContainsNullSets F μ) :
    ∃ Z : ℝ≥0 → Ω → RealL2, (∀ ω,Continuous (fun t => Z t ω)) ∧ StronglyAdapted F Z ∧
      ∀ t (ht : t≤H), Z t=ᵐ[μ] value e P hg U hU M hM t ht := by
  apply ScalarLipschitzContinuousVersion.exists_version hH hn (value e P hg U hU M hM)
    (value_adapted e P hg U hU M hM hn)
    ((NativeScalarBDG.constant 3 : ℝ)*(6*heatConstant (H : ℝ)*(H : ℝ)^(1/4 : ℝ))^8*M)
    (by positivity)
  intro s t hs ht
  rcases le_total s t with hst | hts
  · simpa only [moment,norm_sub_rev,sub_sq_comm] using increment e P hg U hU M hM₀ hM s t hst ht
  · exact increment e P hg U hU M hM₀ hM t s hts hs

end SHEStochastic.ScalarLipschitzTimeMoments
