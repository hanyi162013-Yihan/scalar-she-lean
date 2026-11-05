module

public import SHEStochastic.NativeGirsanovTilt
public import SHEStochastic.NativeExponentialMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeGirsanovPastAlgebra
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open NativeExponential NativeTimeCut NativeCrossEnergy

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

theorem prior_combination (s : ℝ≥0) (u v : Lp C 2 νin) (a : ℝ)
    (hv : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0) :
    prior s (a • v - u) = -prior s u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  apply Lp.ext
  filter_upwards [prior_ae s (a • v - u), prior_ae s u, Lp.coeFn_neg (prior s u),
    Lp.coeFn_sub (a • v) u, Lp.coeFn_smul a v, hv] with p hp hu hn hs hm hv
  rw [hp, hn, Pi.neg_apply, hu]
  by_cases hsp : s < p.1
  · simp [hsp]
  · rw [if_neg hsp, if_neg hsp, hs, Pi.sub_apply, hm, Pi.smul_apply,
      hv (le_of_not_gt hsp), smul_zero, zero_sub]

theorem density_neg (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Lp C 2 νin) : density P e 1 (-u) =ᵐ[μ] density P e (-1) u := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hrow : (-u : Lp C 2 νin) =ᵐ[νin] (fun p ↦ -u p) := Lp.coeFn_neg u
  have hE := NativeEnergy.energy_ae_of_ae _ _ hrow
  have hI : (FiniteCylindricalIto.rawIntegral P.toCoordinates e (-u) : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ -FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω) := by
    rw [map_neg]
    exact Lp.coeFn_neg _
  filter_upwards [hE, hI] with ω hEω hIω
  simp only [norm_neg] at hEω
  change Real.exp (1 * FiniteCylindricalIto.rawIntegral P.toCoordinates e (-u) ω -
    (1 : ℝ) ^ 2 * NativeEnergy.energy (-u) ω / 2) =
      Real.exp (-1 * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω -
        (-1 : ℝ) ^ 2 * NativeEnergy.energy u ω / 2)
  rw [hIω, hEω]
  congr 1
  simp only [one_mul, one_pow, neg_one_mul, neg_one_sq]
  rfl

/-- Tilting a future-supported observation changes no conditional
density in the past. This is the full-past Girsanov calculation. -/
theorem conditional_tilt_density (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s : ℝ≥0) (hsH : s ≤ H) (u v : Lp C 2 νin) (a K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K)
    (hvs : ∀ᵐ p ∂νin, p.1 ≤ s → v p = 0)
    (q : ℝ) (hq : 0 ≤ q) (hv : NativeEnergy.energy v =ᵐ[μ] fun _ ↦ q) :
    μ[density P e 1 (a • v - u) | F s] =ᵐ[μ] μ[density P e (-1) u | F s] := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have hc : ∀ᵐ ω ∂μ, NativeEnergy.energy (a • v - u) ω ≤ 2 * a ^ 2 * q + 2 * K := by
    filter_upwards [energy_combination_le v u a, hv, hu] with ω he hqω huω
    rw [hqω] at he
    exact he.trans (by linarith)
  have hδ := NativeExponentialMartingale.conditional_at_time P e 1 s hsH (a • v - u)
    (2 * a ^ 2 * q + 2 * K) (by positivity) hc
  have hU := NativeExponentialMartingale.conditional_at_time P e (-1) s hsH u K hK hu
  rw [prior_combination s u v a hvs] at hδ
  exact hδ.trans ((density_neg P e (prior s u)).trans hU.symm)

end SHEStochastic.NativeGirsanovPastAlgebra
