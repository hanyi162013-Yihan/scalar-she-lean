module

public import SHEStochastic.FiniteHilbertSquareFormula
public import SHEStochastic.NativeScalarBDG

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeFiniteHilbertBDG
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs Filter
open scoped NNReal ENNReal

variable {Ω C E ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Finite orthonormal Hilbert output satisfies the same moment bound
with no dependence on the number of directions. Only the scalar
lower-moment BDG bound is reused. -/
theorem bounded_moment (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (p : ℕ) (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) B)
    (R : κ → Process (E := C) F μ H) (M : ℝ≥0)
    (hR : ∀ i, ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖R i x‖ ≤ M)
    (v : κ → E) (hv : Orthonormal ℝ v) :
    (∫ ω, ‖FiniteOrthonormalSums.value v
      (fun i ↦ (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (R i) ω)‖ ^ (4 * p) ∂μ) ≤
      (BDGQuadraticEstimate.nextConstant p B : ℝ) *
        ∫ ω, (∑ i, StochasticExponential.bracket F μ H (R i) ω) ^ (2 * p) ∂μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hVersions (i : κ) := NativeBoundedAEVersion.exists_version P e (R i) M (hR i)
  choose X hXc hXa hXp hXm hXr hXmem hXcap using hVersions
  let Y (t : ℝ≥0) (ω : Ω) := FiniteOrthonormalSums.value v (fun i ↦ X i t ω)
  have hYm : Martingale Y F μ := FiniteOrthonormalSums.martingale v X hXm
  have hYc : ∀ᵐ ω ∂μ, Continuous (Y · ω) := by
    filter_upwards [ae_all_iff.mpr hXc] with ω hω
    exact continuous_finsetSum Finset.univ (fun i _ ↦ (hω i).smul continuous_const)
  have hYmem (t : ℝ≥0) (r : ℝ≥0) : MemLp (Y t) r μ :=
    FiniteOrthonormalSums.memLp v (fun i ↦ X i t) r (fun i ↦ hXmem i t r)
  have hYI (t : ℝ≥0) (k : ℕ) (hk : 0 < k) : Integrable (fun ω ↦ ‖Y t ω‖ ^ k) μ :=
    (hYmem t k).integrable_norm_pow hk.ne'
  have hY4p := hYI H (4 * p) (by omega)
  have hT : MemLp (fun ω ↦ ‖Y H ω‖ ^ (2 * p)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (((hYm.stronglyMeasurable H).mono (F.le H)).norm.aestronglyMeasurable.pow (2 * p))).mpr
    change Integrable (fun ω ↦ (‖Y H ω‖ ^ (2 * p)) ^ 2) μ
    simpa only [← pow_mul, show (2 * p) * 2 = 4 * p by omega] using hY4p
  obtain ⟨D, hD, hD0, hDb, hDmax⟩ := DoobAEEnvelope.exists_envelope hYm hYc H (hYmem H 2)
  have hYcap : ∀ᵐ ω ∂μ, ∀ t, Y t ω = Y (min t H) ω := by
    filter_upwards [ae_all_iff.mpr hXcap] with ω hω
    intro t
    apply congrArg (FiniteOrthonormalSums.value v)
    funext i
    exact hω i t
  have hDY : ∀ᵐ ω ∂μ, ∀ t, ‖Y t ω‖ ≤ D ω := by
    filter_upwards [hYcap, hDb] with ω hcω hbω
    intro t
    rw [hcω t]
    exact hbω (min t H) (min_le_right t H)
  obtain ⟨hDp, hDpBound⟩ := DoobAEEnvelope.bound hYm hYc H D hD hD0 hDb hDmax (2 * p)
    (fun t ↦ hYI t (2 * p) (by omega)) hT
  obtain ⟨V, hV, hSquare, hVB⟩ := FiniteHilbertSquareFormula.exists_input P e R M hR v hv X hXa hXp
    (fun i ↦ (hXc i).mono fun _ hω ↦ hω.continuousOn) hXr D hD hD0 hDY
  let A (ω : Ω) := ∑ i, StochasticExponential.bracket F μ H (R i) ω
  have hA0 (ω : Ω) : 0 ≤ A ω := Finset.sum_nonneg fun i _ ↦ WeightedBracketBound.bracket_nonneg (R i) ω
  have hAm : Measurable A := Finset.measurable_sum _ (fun i _ ↦ StochasticExponential.bracket_measurable F μ H (R i))
  let K : ℝ := ∑ _i : κ, (timeMeasure H).real Set.univ * (M : ℝ) ^ 2
  have hAb : ∀ᵐ ω ∂μ, A ω ≤ K := by
    filter_upwards [ae_all_iff.mpr (fun i ↦ WeightedBracketBound.bounded (R i) M M.property (hR i))] with ω hω
    exact Finset.sum_le_sum (fun i _ ↦ hω i)
  have hAp : MemLp (fun ω ↦ A ω ^ p) 2 μ := by
    apply MemLp.of_bound (hAm.pow_const p).stronglyMeasurable.aestronglyMeasurable (K ^ p)
    filter_upwards [hAb] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (hA0 ω) p)]
    exact pow_le_pow_left₀ (hA0 ω) hω p
  have hX0 (i : κ) : X i 0 =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    have hh := hXr i 0
    rw [NNReal.coe_zero, stop_zero, map_zero] at hh
    exact hh.trans (Lp.coeFn_zero _ _ _)
  have hY0 : ∀ᵐ ω ∂μ, Y 0 ω = 0 := by
    filter_upwards [ae_all_iff.mpr hX0] with ω hω
    simp only [Y, FiniteOrthonormalSums.value, hω, zero_smul, Finset.sum_const_zero]
  have hSquare' : ∀ᵐ ω ∂μ, ‖Y H ω‖ ^ 2 = 2 * J.integral V ω + A ω := by
    filter_upwards [hSquare, hY0] with ω hs hz
    change ‖Y H ω‖ ^ 2 - ‖Y 0 ω‖ ^ 2 = _ at hs
    simpa only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using hs
  have hFinal := BDGQuadraticEstimate.estimate p B J hBDG (fun ω ↦ ‖Y H ω‖) A D V hD0 hA0
    (by simpa only [norm_norm] using hY4p) hAp hDp
    (by simpa only [norm_norm, show 2 * (2 * p) = 4 * p by omega] using hDpBound) hVB hSquare'
  simp only [norm_norm] at hFinal
  have hEnd : Y H =ᵐ[μ] (fun ω ↦ FiniteOrthonormalSums.value v (fun i ↦ J.integral (R i) ω)) := by
    have hr (i : κ) : X i H =ᵐ[μ] J.integral (R i) := by
      have hh := hXr i H
      rwa [FiniteItoStoppedVersions.stop_horizon] at hh
    filter_upwards [ae_all_iff.mpr hr] with ω hω
    apply congrArg (FiniteOrthonormalSums.value v)
    funext i
    exact hω i
  have hEI : (∫ ω, ‖Y H ω‖ ^ (4 * p) ∂μ) =
      ∫ ω, ‖FiniteOrthonormalSums.value v (fun i ↦ J.integral (R i) ω)‖ ^ (4 * p) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hEnd] with ω hω
    rw [hω]
  rwa [hEI] at hFinal

end SHEStochastic.NativeFiniteHilbertBDG
