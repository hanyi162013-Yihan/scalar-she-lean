module

public import SHEStochastic.NativeFourierHeatCoordinate
public import SHEStochastic.StateNoiseCovariance
public import SHEStochastic.HolderCoefficientEnergyGrowth
public import SHE.NativeFourierNoiseRows
public import SHE.HeatTrace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarHeatFourierEnergy
open MeasureTheory SHE SHE.DyadicApproximation SHE.StoppedFourier SHE.PredictableL2 AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local notation "w" => NativeFourierHeatCoordinate.weight

/-- Parseval for the actual scalar state and the two real test rows
of each complex Fourier character. -/
theorem state_energy (u : RealL2) :
    Summable (fun n : ℤ => (φ Complex.reCLM n u)^2+(φ Complex.imCLM n u)^2) ∧
      (∑' n : ℤ,((φ Complex.reCLM n u)^2+(φ Complex.imCLM n u)^2))=‖u‖^2 := by
  have h : Summable (fun n : ℤ => ‖NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u)‖^2) ∧
      (∑' n : ℤ,‖NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u)‖^2)=
        ‖NativeHeatObservation.embed u‖^2 :=
    HilbertTrace.basis_sq (_root_.fourierBasis (T := 2*Real.pi)) (NativeHeatObservation.embed u)
  have he (n : ℤ) : (φ Complex.reCLM n u)^2+(φ Complex.imCLM n u)^2 =
      ‖NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u)‖^2 := by
    let z := NativeFourierNoiseRows.coefficient n (NativeHeatObservation.embed u)
    change z.re^2+z.im^2=‖z‖^2
    rw [Complex.sq_norm,Complex.normSq_apply]
    ring
  simpa only [he,NativeHeatObservation.embed_norm] using h

/-- The real and imaginary spatial weights together have unit square
at every spatial point, retaining the signed coefficient in each row. -/
theorem row_energy {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
    (hβ : 0<β) (hβ₁ : β≤1) (u : Noise) (n : ℤ) :
    ‖StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.reCLM n) u‖^2+
      ‖StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.imCLM n) u‖^2 =
      ‖HolderCoefficientIntegrability.coefficient hβ hβ₁ hg u‖^2 := by
  let A := StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.reCLM n) u
  let B := StateNoiseCovariance.row ν hβ hβ₁ hg (w Complex.imCLM n) u
  change ‖A‖^2+‖B‖^2=_
  rw [realLp_norm_sq,realLp_norm_sq,realLp_norm_sq,←integral_add
    (Lp.memLp A).norm.integrable_sq (Lp.memLp B).norm.integrable_sq]
  apply integral_congr_ae
  filter_upwards [StateNoiseCovariance.row_ae ν hβ hβ₁ hg (w Complex.reCLM n) u,
    StateNoiseCovariance.row_ae ν hβ hβ₁ hg (w Complex.imCLM n) u,
    HolderCoefficientIntegrability.coefficient_ae hβ hβ₁ hg u] with x ha hb hgx
  change A x=_ at ha
  change B x=_ at hb
  simp only [ha,hb,hgx,Real.norm_eq_abs,sq_abs,smul_eq_mul]
  have he : (w Complex.reCLM n x)^2+(w Complex.imCLM n x)^2=1 := by
    let z : ℂ := fourier (-n) x
    change (1*z.re)^2+(1*z.im)^2=1
    have hz : ‖z‖=1 := by simp [z,fourier_apply]
    have hs := Complex.sq_norm z
    rw [hz,Complex.normSq_apply] at hs
    nlinarith
  nlinarith [congrArg (fun t : ℝ => t*(g (u x))^2) he]

/-- The physical heat-row trace has the integrable inverse-square-root
age envelope, with the exact Fourier damping retained on the left. -/
theorem trace {τ : ℝ} (hτ : 0<τ) :
    Summable (fun n : ℤ => Real.exp (-(2*τ)*(n : ℝ)^2)) ∧
      (∑' n : ℤ,Real.exp (-(2*τ)*(n : ℝ)^2))≤
        1+2*HeatTrace.fractionalGaussianIntegral 0*(2*τ)^(-(1/2 : ℝ)) := by
  have ht : 0<2*τ := mul_pos (by norm_num) hτ
  have hs := HeatTrace.multiplier_int_summable (Λ := 1) (ρ := 0)
    (by norm_num) (by norm_num) ht
  have he := HeatTrace.centered_heat_trace_bound (Λ := 1) (ρ := 0)
    (by norm_num) (by norm_num) (by norm_num) ht
  simpa only [HeatTrace.multiplier,neg_zero,Real.rpow_zero,one_mul,zero_sub] using And.intro hs he

end SHEStochastic.ScalarHeatFourierEnergy
