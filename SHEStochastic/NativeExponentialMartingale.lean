module

public import SHEStochastic.NativePastExponential
public import SHEStochastic.NativeTimeCut

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeExponentialMartingale
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open NativeExponential NativeTimeCut

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "νin" => FiniteScalarIto.inputMeasure F μ H

theorem density_prior_adapted (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (s : ℝ≥0) (u : Lp C 2 νin) :
    AEStronglyMeasurable[F s] (density P e a (prior s u)) μ := by
  have hI := FiniteCylindricalIto.rawIntegral_adapted P e s (prior s u) (prior_supported s u)
  let X := hI.mk (FiniteCylindricalIto.rawIntegral P.toCoordinates e (prior s u))
  let Z (ω : Ω) := Real.exp (a * X ω - a ^ 2 * priorEnergy s u ω / 2)
  have hc : Continuous (fun p : ℝ × ℝ ↦ Real.exp (a * p.1 - a ^ 2 * p.2 / 2)) := by fun_prop
  have hZ : StronglyMeasurable[F s] Z :=
    hc.comp_stronglyMeasurable (hI.stronglyMeasurable_mk.prodMk (priorEnergy_adapted s u))
  have he : density P e a (prior s u) =ᵐ[μ] Z := by
    filter_upwards [hI.ae_eq_mk, energy_prior_ae s u] with ω hω hE
    change Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (prior s u) ω -
      a ^ 2 * NativeEnergy.energy (prior s u) ω / 2) =
        Real.exp (a * X ω - a ^ 2 * priorEnergy s u ω / 2)
    rw [hω, hE]
  exact hZ.aestronglyMeasurable.congr he.symm

theorem density_split (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (s : ℝ≥0) (u : Lp C 2 νin) :
    density P e a u =ᵐ[μ]
      (fun ω ↦ density P e a (prior s u) ω * density P e a (after s u) ω) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have he : FiniteCylindricalIto.rawIntegral P.toCoordinates e u =
      FiniteCylindricalIto.rawIntegral P.toCoordinates e (prior s u) +
        FiniteCylindricalIto.rawIntegral P.toCoordinates e (after s u) := by
    rw [← map_add, NativeTimeCut.split]
  have hi : (FiniteCylindricalIto.rawIntegral P.toCoordinates e u : Ω → ℝ) =ᵐ[μ]
      (fun ω ↦ FiniteCylindricalIto.rawIntegral P.toCoordinates e (prior s u) ω +
        FiniteCylindricalIto.rawIntegral P.toCoordinates e (after s u) ω) := by
    rw [he]
    exact Lp.coeFn_add _ _
  filter_upwards [hi, energy_split s u] with ω hI hE
  change Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e u ω -
      a ^ 2 * NativeEnergy.energy u ω / 2) = _
  rw [hI, hE]
  change _ = Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (prior s u) ω -
    a ^ 2 * NativeEnergy.energy (prior s u) ω / 2) *
      Real.exp (a * FiniteCylindricalIto.rawIntegral P.toCoordinates e (after s u) ω -
        a ^ 2 * NativeEnergy.energy (after s u) ω / 2)
  rw [← Real.exp_add]
  congr 1
  ring

/-- Conditional density identity in the original filtration. In
particular the bounded-energy exponential is a genuine martingale,
without a Novikov or Girsanov theorem among the inputs. -/
theorem conditional_at_time (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (a : ℝ) (s : ℝ≥0) (hsH : s ≤ H) (u : Lp C 2 νin) (K : ℝ) (hK : 0 ≤ K)
    (hu : ∀ᵐ ω ∂μ, NativeEnergy.energy u ω ≤ K) :
    μ[density P e a u | F s] =ᵐ[μ] density P e a (prior s u) := by
  have hpost : ∀ᵐ ω ∂μ, NativeEnergy.energy (after s u) ω ≤ K :=
    (energy_after_le s u).trans hu
  have hCE := NativePastExponential.conditional_mean_one P e a s hsH (after s u)
    (after_supported s u) K hK hpost
  have huI := (NativeBoundedExponential.bounded_energy P e a u K hK hu).1.integrable (by norm_num)
  have hpI := (NativeBoundedExponential.bounded_energy P e a (after s u) K hK hpost).1.integrable
    (by norm_num)
  have hm := density_prior_adapted P e a s u
  let φ := hm.mk (density P e a (prior s u))
  have hφ : StronglyMeasurable[F s] φ := hm.stronglyMeasurable_mk
  have hprod : (fun ω ↦ φ ω * density P e a (after s u) ω) =ᵐ[μ] density P e a u := by
    filter_upwards [hm.ae_eq_mk, density_split P e a s u] with ω hω hs
    change φ ω * density P e a (after s u) ω = _
    change density P e a (prior s u) ω = φ ω at hω
    rw [← hω]
    exact hs.symm
  have hprodI := huI.congr hprod.symm
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℝ) hφ hprodI hpI
  change μ[fun ω ↦ φ ω * density P e a (after s u) ω | F s] =ᵐ[μ]
    (fun ω ↦ φ ω * μ[density P e a (after s u) | F s] ω) at hp
  apply (condExp_congr_ae hprod).symm.trans
  apply hp.trans
  filter_upwards [hCE, hm.ae_eq_mk] with ω hω hφω
  change φ ω * μ[density P e a (after s u) | F s] ω = _
  rw [hω, mul_one]
  exact hφω.symm

end SHEStochastic.NativeExponentialMartingale
