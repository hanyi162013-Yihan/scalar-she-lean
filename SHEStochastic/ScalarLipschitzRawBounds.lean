module

public import SHEStochastic.ScalarLipschitzConvolution
public import SHEStochastic.ScalarLipschitzAgeDensity
public import SHEStochastic.ScalarLipschitzItoMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarLipschitzRawBounds
open MeasureTheory Set Filter SHE SHE.PredictableL2 SHE.StoppedFourier SHE.DyadicApproximation SHE.FiniteHaar AddCircle
open ScalarLipschitzHeatColumn ScalarLipschitzHeatColumns ScalarLipschitzKernelBounds ScalarLipschitzConvolution
  ScalarLipschitzItoMoment
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
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩
local instance : SecondCountableTopology Noise :=
  NativePhysicalState.equivalence.symm.toHomeomorph.secondCountableTopology

def growth (g : ℝ → ℝ) (C : ℝ≥0) : ℝ := 4*(‖g 0‖+(C : ℝ))^2

theorem growth_nonneg (g : ℝ → ℝ) (C : ℝ≥0) : 0≤growth g C := by
  unfold growth
  positivity

theorem coefficient_sq {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g) (u : RealL2) :
    ‖coefficient hg u‖^2≤growth g C*(1+‖u‖^2) := by
  simpa only [coefficient,growth,LinearIsometry.norm_map] using
    HolderCoefficientEnergyGrowth.coefficient_bound ν hg zero_lt_one le_rfl (NativePhysicalState.push u)

theorem pow_add_bound (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (n : ℕ) :
    (a+b)^n ≤ 2^n*(a^n+b^n) := by
  have h : a+b≤2*max a b := by linarith [le_max_left a b,le_max_right a b]
  apply (pow_le_pow_left₀ (add_nonneg ha hb) h n).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (pow_nonneg ha _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (pow_nonneg hb _)

theorem sq_le_one_add_sixteen {a : ℝ} (ha : 0≤a) : a^2≤1+a^16 := by
  by_cases h : a≤1
  · exact (pow_le_one₀ ha h).trans (le_add_of_nonneg_right (pow_nonneg ha _))
  · exact (pow_le_pow_right₀ (le_of_not_ge h) (by decide : (2 : ℕ)≤16)).trans
      (le_add_of_nonneg_left zero_le_one)

variable {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
local instance : MeasurableSpace (HilbertColumns.Space I RealL2) := borel _
local instance : BorelSpace (HilbertColumns.Space I RealL2) := ⟨rfl⟩
variable
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (e : HilbertBasis I ℝ Noise)
  {g : ℝ → ℝ} {C : ℝ≥0} (hg : HolderWith C 1 g)
  (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[F.predictable] (Function.uncurry U))

def coeffSquare (p : ℝ≥0×Ω) : ℝ≥0∞ := ENNReal.ofReal (‖coefficient hg (U p.1 p.2)‖^2)

include hU in
theorem coeffSquare_measurable : Measurable (coeffSquare hg U) :=
  (((coefficient_continuous hg).comp_stronglyMeasurable
    (hU.mono (predictable_le_product F))).norm.pow 2).measurable.ennreal_ofReal

theorem coeffSquare_eighth (t : ℝ≥0) (hUt : Measurable (U t)) :
    (∫⁻ ω,(coeffSquare hg U (t,ω))^8 ∂μ)≤
      ENNReal.ofReal ((growth g C)^8*2^8)*(1+moment 16 (U t) μ) := by
  have hG : 0≤growth g C := growth_nonneg g C
  calc
    _ ≤ ∫⁻ ω,ENNReal.ofReal ((growth g C)^8*2^8)*(1+ENNReal.ofReal (‖U t ω‖^16)) ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only [coeffSquare]
      rw [←ENNReal.ofReal_pow (sq_nonneg _),←ENNReal.ofReal_one,
        ←ENNReal.ofReal_add zero_le_one (by positivity),←ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have h := pow_le_pow_left₀ (sq_nonneg _) (coefficient_sq hg (U t ω)) 8
      rw [mul_pow] at h
      apply h.trans
      have h' := pow_add_bound 1 (‖U t ω‖^2) zero_le_one (sq_nonneg _) 8
      rw [one_pow,←pow_mul] at h'
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h' (pow_nonneg hG _)
    _ = _ := by
      have hM : Measurable (fun ω => ENNReal.ofReal (‖U t ω‖^16)) :=
        (hUt.norm.pow_const _).ennreal_ofReal
      have hA : Measurable (fun ω => 1+ENNReal.ofReal (‖U t ω‖^16)) :=
        measurable_const.add hM
      rw [lintegral_const_mul'' (ENNReal.ofReal ((growth g C)^8*2^8)) hA.aemeasurable,
        lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
      rfl

theorem coeffSquare_second {t : ℝ≥0} {M : ℝ≥0∞}
    (hM : (∫⁻ ω,(coeffSquare hg U (t,ω))^8 ∂μ)≤M) :
    (∫⁻ ω,coeffSquare hg U (t,ω) ∂μ)≤1+M := by
  calc
    _ ≤ ∫⁻ ω,1+(coeffSquare hg U (t,ω))^8 ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only [coeffSquare]
      rw [←ENNReal.ofReal_pow (sq_nonneg _),←ENNReal.ofReal_one,
        ←ENNReal.ofReal_add zero_le_one (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [←pow_mul]
      exact sq_le_one_add_sixteen (norm_nonneg _)
    _ ≤ _ := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
      exact add_le_add le_rfl hM

omit [MeasurableSpace Ω] [Countable I] in
theorem increment_envelope {s t : ℝ≥0} (hst : s≤t) (ht : t≤H) (p : ℝ≥0×Ω) :
    ENNReal.ofReal (‖raw e hg U t p-raw e hg U s p‖^2)≤
      ScalarLipschitzAgeDensity.density (heatConstant (H : ℝ)) s t p.1*coeffSquare hg U p := by
  unfold ScalarLipschitzAgeDensity.density
  by_cases hp : p.1<s
  · rw [ite_eq_left hp,coeffSquare,←ENNReal.ofReal_mul (by
      have hδ : 0≤(t : ℝ)-(s : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
      exact mul_nonneg (mul_nonneg (heatConstant_nonneg H.property) (Real.rpow_nonneg hδ _))
        (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hp.le)) _))]
    apply ENNReal.ofReal_le_ofReal
    have h := increment_bound e (a := coefficient hg (U p.1 p.2))
      (sub_pos.mpr (show (p.1 : ℝ)<s by exact_mod_cast hp))
      ((sub_le_self _ p.1.property).trans (show (s : ℝ)≤H by exact_mod_cast hst.trans ht))
      (sub_nonneg.mpr (show (s : ℝ)≤t by exact_mod_cast hst))
    rw [show (s : ℝ)-(p.1 : ℝ)+((t : ℝ)-(s : ℝ))=(t : ℝ)-(p.1 : ℝ) by ring] at h
    exact h
  · rw [ite_eq_right hp,raw_zero e hg U s (le_of_not_gt hp),sub_zero]
    by_cases hp' : p.1<t
    · have ha : 0≤(t : ℝ)-(p.1 : ℝ) := sub_nonneg.mpr (by exact_mod_cast hp'.le)
      have hA : 0≤heatConstant (H : ℝ)*((t : ℝ)-(p.1 : ℝ))^(-(1/2 : ℝ)) :=
        mul_nonneg (heatConstant_nonneg H.property) (Real.rpow_nonneg ha _)
      rw [ite_eq_left hp',coeffSquare,←ENNReal.ofReal_mul hA]
      exact ENNReal.ofReal_le_ofReal (kernel_bound e
        (sub_pos.mpr (by exact_mod_cast hp'))
        ((sub_le_self _ p.1.property).trans (by exact_mod_cast ht)) _)
    · simp only [ite_eq_right hp',raw_zero e hg U t (le_of_not_gt hp'),norm_zero,zero_pow (by decide : 2≠0),
        ENNReal.ofReal_zero,zero_mul,le_refl]

include hU in
theorem raw_integrable {M : ℝ≥0∞} (hMt : M≠⊤)
    (hM : ∀ᵐ s ∂PredictableL2.timeMeasure H,(∫⁻ ω,(coeffSquare hg U (s,ω))^8 ∂μ)≤M)
    (t : ℝ≥0) (ht : t≤H) :
    Integrable (fun p => ‖raw e hg U t p‖^2) (energyMeasure μ H) := by
  let K := heatConstant (H : ℝ)
  apply integrable_of_density (raw e hg U t) (raw_measurable e hg U hU t).stronglyMeasurable
    (ScalarLipschitzAgeDensity.density K 0 t) (ScalarLipschitzAgeDensity.measurable K 0 t)
    (coeffSquare hg U) (coeffSquare_measurable hg U hU) (1+M) (ENNReal.add_ne_top.mpr ⟨by simp,hMt⟩)
    (hM.mono (fun _ h => coeffSquare_second hg U h))
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (ScalarLipschitzAgeDensity.mass (heatConstant_nonneg H.property) bot_le ht)
  · apply Filter.Eventually.of_forall
    intro p
    simpa only [raw_zero e hg U 0 (show (0 : ℝ≥0)≤p.1 from zero_le),sub_zero] using increment_envelope e hg U (s := 0) (show (0 : ℝ≥0)≤t from zero_le) ht p

end SHEStochastic.ScalarLipschitzRawBounds
