module

public import SHEStochastic.NativePowerMomentFromEnvelope
public import SHEStochastic.PowerMomentAbsorption
public import SHEStochastic.DoobAEEnvelope
public import SHEStochastic.BDGBoundedReduction
public import SHEStochastic.BDGSecondMoment
public import SHEStochastic.BDGRealMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeScalarBDGAll
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs Filter
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Every integer even moment, proved using the existing native
quadratic variation, martingale and Doob estimates. -/
theorem bounded_moment (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (p : ℕ) (hp : 2 ≤ p) (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M) :
    (∫ ω, ‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω‖^(2*p) ∂μ) ≤
      (PowerMomentAbsorption.constant p : ℝ)*∫ ω, StochasticExponential.bracket F μ H u ω^p ∂μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨Y, hYc, hYa, hYp, hYm, hYr, hMem, hCap⟩ := NativeBoundedAEVersion.exists_version P e u M hu
  have hL (t : ℝ≥0) (k : ℕ) : MemLp (fun ω ↦ Y t ω^k) 2 μ := by
    by_cases hk : k=0
    · subst k
      simpa only [pow_zero] using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω ↦ (1 : ℝ)) 2 μ)
    apply (memLp_two_iff_integrable_sq (((hYa t).mono (F.le t)).aestronglyMeasurable.pow k)).mpr
    have hi := (hMem t ((2*k : ℕ) : ℝ≥0)).integrable_norm_pow (by omega : 2*k ≠ 0)
    convert hi using 1
    funext ω
    change (Y t ω^k)^2=‖Y t ω‖^(2*k)
    rw [← pow_mul, Nat.mul_comm k 2]
    simp only [pow_mul, Real.norm_eq_abs, sq_abs]
  have hYI (t : ℝ≥0) (r : ℕ) : Integrable (fun ω ↦ ‖Y t ω‖^r) μ := by
    simpa only [norm_pow] using ((hL t r).integrable one_le_two).norm
  have hT (r : ℕ) : MemLp (fun ω ↦ ‖Y H ω‖^r) 2 μ := by
    simpa only [norm_pow] using (hL H r).norm
  have hY2 : MemLp (Y H) 2 μ := by simpa only [pow_one] using hL H 1
  obtain ⟨D, hD, hD0, hDb, hDmax⟩ := DoobAEEnvelope.exists_envelope hYm hYc H hY2
  have hDpow (r : ℕ) := DoobAEEnvelope.bound hYm hYc H D hD hD0 hDb hDmax r (fun t ↦ hYI t r) (hT r)
  let A := StochasticExponential.bracket F μ H u
  let K : ℝ := (timeMeasure H).real Set.univ*(M : ℝ)^2
  have hA0 (ω : Ω) : 0 ≤ A ω := WeightedBracketBound.bracket_nonneg u ω
  have hAb : ∀ᵐ ω ∂μ, A ω ≤ K := WeightedBracketBound.bounded u M M.coe_nonneg hu
  have hAp (r : ℕ) : MemLp (fun ω ↦ A ω^r) 2 μ := by
    apply MemLp.of_bound ((StochasticExponential.bracket_measurable F μ H u).pow_const r).stronglyMeasurable.aestronglyMeasurable (K^r)
    filter_upwards [hAb] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (hA0 ω) r)]
    exact pow_le_pow_left₀ (hA0 ω) hω r
  have hA : MemLp A 2 μ := by simpa only [pow_one] using hAp 1
  have hD2p : Integrable (fun ω ↦ D ω^(2*p)) μ := by
    simpa only [← pow_mul, Nat.mul_comm p 2] using (hDpow p).1.integrable_sq
  have hDA : Integrable (fun ω ↦ D ω^(2*p-2)*A ω) μ := (hDpow (2*p-2)).1.integrable_mul hA
  have hFirst := NativePowerMomentFromEnvelope.estimate P e u M hu Y hYm hYr hL (2*p)
    (by omega) D hD0 (by simpa only [Real.norm_eq_abs] using hDb) (hDpow (2*p-2)).1
  have hEven (ω : Ω) : Y H ω^(2*p)=‖Y H ω‖^(2*p) := by
    rw [pow_mul, pow_mul, Real.norm_eq_abs, sq_abs]
  simp_rw [hEven] at hFirst
  have hFinal := PowerMomentAbsorption.estimate p (by omega) D A hD0 hA0 hD2p
    ((hAp p).integrable one_le_two) hDA (∫ ω, ‖Y H ω‖^(2*p) ∂μ) (hDpow p).2 hFirst
  have hEnd : Y H =ᵐ[μ] J.integral u := by
    have hh := hYr H
    rwa [FiniteItoStoppedVersions.stop_horizon] at hh
  have he : (∫ ω, ‖Y H ω‖^(2*p) ∂μ) = ∫ ω, ‖J.integral u ω‖^(2*p) ∂μ :=
    integral_congr_ae (hEnd.mono fun ω hω ↦ by
      change ‖Y H ω‖^(2*p)=‖J.integral u ω‖^(2*p)
      rw [hω])
  rwa [he] at hFinal

def constant (p : ℕ) : ℝ≥0 := if p=1 then 1 else PowerMomentAbsorption.constant p

/-- Scalar native BDG for every positive integer moment order, on the
same original filtration and without a null-completeness assumption. -/
theorem power (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (p : ℕ) (hp : 0 < p) :
    StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) (constant p) := by
  by_cases h1 : p=1
  · subst p
    simpa [constant] using BDGSecondMoment.power_one (FiniteCylindricalIto.terminalIto P.toCoordinates e)
  have hp2 : 2 ≤ p := by omega
  simp only [constant, if_neg h1]
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  apply BDGBoundedReduction.of_bounded
  intro u n hu
  let M : ℝ≥0 := n
  have huM : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M := hu
  have hLp := NativeBoundedMoments.memLp_stopped P e u M huM H ((2*p : ℕ) : ℝ≥0)
  rw [FiniteItoStoppedVersions.stop_horizon] at hLp
  have hOut : Integrable (fun ω ↦ ‖J.integral u ω‖^(2*p)) μ := hLp.integrable_norm_pow (by omega)
  let K : ℝ := (timeMeasure H).real Set.univ*(M : ℝ)^2
  have hA : Integrable (fun ω ↦ StochasticExponential.bracket F μ H u ω^p) μ := by
    apply Integrable.of_bound ((StochasticExponential.bracket_measurable F μ H u).pow_const p).stronglyMeasurable.aestronglyMeasurable (K^p)
    filter_upwards [WeightedBracketBound.bounded u M M.coe_nonneg huM] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (WeightedBracketBound.bracket_nonneg u ω) p)]
    exact pow_le_pow_left₀ (WeightedBracketBound.bracket_nonneg u ω) hω p
  exact BDGRealMoments.of_real_bound p J _ u hOut hA (bounded_moment P e p hp2 u M huM)

end SHEStochastic.NativeScalarBDGAll
