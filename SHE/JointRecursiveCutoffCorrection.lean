module

public import SHE.CutoffWeightedDerivatives
public import SHE.UncutHistoryMass
public import SHE.JointBoundaryStripBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.JointRecursiveCutoffCorrection
open Set MeasureTheory Filter Topology StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories JointCutoffStep JointCutoffBoundary
open PhysicalRemainderMass CutoffUncutComparison CutoffWeightedDerivatives
open Classical
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R P n) (Λ : ℝ)
variable {U V : Ω×ℝ→CircleL2} (hU : Measurable U) (hV : Measurable V)
variable {XU XV : Ω×(ℝ×HeatCircle)→ℝ} (hXU : Measurable XU) (hXV : Measurable XV)
include hU hV hXU hXV

/-- This bound applies to the actual recursively δ-dependent test.
Its constant is independent of δ, while its smooth coefficient and
finite-depth dependence remains explicit. -/
theorem weighted_correction_bound (k : ℕ) : ∃ K : ℝ, 0≤K ∧
    ∀ (δ : ℝ) (hδ : 0<δ) p ω,
      ‖correction (RecursiveHeatBounds.level L δ hδ 0 k) Λ δ U V XU XV p ω‖≤
        K*UncutSmoothWords.weight L k p*heatMass δ := by
  obtain ⟨A,hAn,hA⟩ := (UniformSmooth.UniformBoundedSmooth.fixed (P := Unit) R.totalVariance_smooth).norm_bound
  obtain ⟨M,hMn,hM⟩ := CutoffUncutComparison.test_norm_bound L k
  obtain ⟨D,hDn,hD⟩ := fderiv_bound L k
  obtain ⟨B,hBn,hB⟩ := hessian_bound L k
  let K : ℝ := (1/2:ℝ)*(A+R.upper)*B*((n+k : ℕ) : ℝ)
  have hKn : 0≤K := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAn R.upper_nonneg)) hBn) (Nat.cast_nonneg _)
  refine ⟨K,hKn,fun δ hδ p ω => ?_⟩
  rw [JointCutoffBoundary.correction_eq_strip _ Λ hU hV hXU hXV δ hδ]
  have hh := JointBoundaryStripBound.strip_bound (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV
    hAn (fun z => by simpa only [Real.norm_eq_abs] using hA () z)
    (mul_nonneg hBn (UncutSmoothWords.weight_nonneg L k p)) hδ.le p ω
    (hM δ hδ p) (hD δ hδ p) (hB δ hδ p)
  convert hh using 1 <;> dsimp [K] <;> ring


def mass (μ : Measure P) (τ : Measure Ω) (k : ℕ) (δ : ℝ) : ℝ :=
  if hδ : 0<δ then ∫ q : History P k×Ω,
    correction (RecursiveHeatBounds.level L δ hδ 0 k) Λ δ U V XU XV q.1 q.2
      ∂(historyMeasure R μ k).prod τ else 0

/-- Actual moving recursive cutoff corrections vanish in full expected
history mass. The result is for every fixed smooth depth, with no
rough-coefficient or infinite-order uniformity asserted. -/
theorem mass_tendsto_zero (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (k : ℕ) : Tendsto (mass L Λ (U := U) (V := V) (XU := XU) (XV := XV) μ τ k) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨K,hKn,hK⟩ := weighted_correction_bound L Λ hU hV hXU hXV k
  let W : ℝ := ∫ p : History P k, UncutSmoothWords.weight L k p ∂historyMeasure R μ k
  have ht : Tendsto (fun δ : ℝ => K*W*heatMass δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := ((continuous_const (y := K*W)).mul PhysicalBoundaryStrip.continuous_heatMass).tendsto (0:ℝ)
    have hres := hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    change Tendsto (fun δ : ℝ => K*W*heatMass δ) (𝓝[>] (0:ℝ)) (𝓝 (K*W*heatMass 0)) at hres
    simpa only [heatMass,Real.zero_rpow (by norm_num : (1/2:ℝ)≠0),mul_zero,add_zero] using hres
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0<δ at hδ
  rw [mass,dif_pos hδ]
  have hdom := ((UncutHistoryMass.weight_integrable L μ k).comp_fst τ).const_mul (K*heatMass δ)
  have hb := norm_integral_le_of_norm_le hdom (Eventually.of_forall (fun q : History P k×Ω => by
    have hh := hK δ hδ q.1 q.2
    convert hh using 1 <;> ring))
  apply hb.trans_eq
  rw [integral_const_mul,integral_prod _ ((UncutHistoryMass.weight_integrable L μ k).comp_fst τ)]
  simp only [integral_const,probReal_univ,one_smul]
  dsimp [W]
  ring

end SHE.JointRecursiveCutoffCorrection
