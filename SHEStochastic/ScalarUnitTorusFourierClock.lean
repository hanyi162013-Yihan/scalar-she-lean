module

public import SHEStochastic.BoundedFourierInput
public import SHEStochastic.NativeTimeDilatedFamily
public import SHE.NativeClock
public import SHE.ClockedItoAlgebra
public import SHE.TimeDilationPathPull

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnitTorusFourierClock
open MeasureTheory SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation
  AddCircle UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν₂
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

/-- Brownian normalization of a diffusion for the native clock. -/
def scale : ℝ := (Real.sqrt (r : ℝ))⁻¹

theorem scale_pos : 0<scale := inv_pos.mpr (Real.sqrt_pos.mpr hr)

def nativeCoefficient (g : ℝ → ℝ) : ℝ → ℝ := scale • g

theorem holder {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) :
    HolderWith (C*‖scale‖₊) β (nativeCoefficient g) :=
  hg.smul scale

def nativeBound (B : ℝ≥0) : ℝ≥0 := ‖scale‖₊*B

theorem bounded {g : ℝ → ℝ} {B : ℝ≥0} (hb : ∀ z,‖g z‖≤B) (z : ℝ) :
    ‖nativeCoefficient g z‖≤nativeBound B := by
  change ‖scale • g z‖≤‖scale‖*(B : ℝ)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)

theorem elliptic {g : ℝ → ℝ} {c : ℝ} (he : ∀ z,c≤|g z|) (z : ℝ) :
    scale*c≤|nativeCoefficient g z| := by
  change scale*c≤|scale*g z|
  rw [abs_mul,abs_of_pos scale_pos]
  exact mul_le_mul_of_nonneg_left (he z) scale_pos.le

theorem heat (t : ℝ≥0) :
    NativeHeatObservation.heat (clock r hr t : ℝ≥0) = RealHeat.realHeat (t : ℝ) := by
  rw [←NativeClock.heat_time]
  change RealHeat.realHeat ((clock r hr).symm (clock r hr t) : ℝ≥0) = _
  rw [OrderIso.symm_apply_apply]

private theorem row_scale {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
    (hβ : 0<β) (hβ₁ : β≤1) (k : C(AddCircle (2*Real.pi),ℝ)) (u : Noise) :
    Real.sqrt (r : ℝ) • StateNoiseCovariance.row ν₂ hβ hβ₁ (holder hg) k u =
      StateNoiseCovariance.row ν₂ hβ hβ₁ hg k u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Real.sqrt (r : ℝ))
      (StateNoiseCovariance.row ν₂ hβ hβ₁ (holder hg) k u),
    StateNoiseCovariance.row_ae ν₂ hβ hβ₁ (holder hg) k u,
    StateNoiseCovariance.row_ae ν₂ hβ hβ₁ hg k u] with x hs hn hp
  rw [hs]
  change Real.sqrt (r : ℝ) • (StateNoiseCovariance.row ν₂ hβ hβ₁ (holder hg) k u) x = _
  rw [hn,hp]
  change Real.sqrt (r : ℝ) * (k x * (scale * g (u x))) = k x * g (u x)
  unfold scale
  field_simp [(Real.sqrt_pos.mpr (show (0 : ℝ)<r from hr)).ne']

variable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

local notation "Fₙ" => filtration F (clock r hr)
local notation "Hₙ" => r*H

/-- Actual Fourier test against spatial white noise of unit Haar mass
for the heat equation with generator ∂² on the unit circle. -/
def row (W : ℝ≥0 → Ω → RealL2) {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g)
    (hβ : 0<β) (hβ₁ : β≤1) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (p : ℝ≥0 × Ω) : Noise :=
  Real.exp ((r : ℝ)*min (p.1 : ℝ) (H : ℝ)*(n : ℝ)^2) •
    StateNoiseCovariance.row ν₂ hβ hβ₁ hg (NativeFourierHeatCoordinate.weight a n) (physical W p)

variable (U : ℝ≥0 → Ω → RealL2)
  (hU : StronglyMeasurable[(PredictableTimeDilation.filtration F
    (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos)).predictable] (Function.uncurry U))
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β<1)
  (B : ℝ≥0) (hb : ∀ z,‖g z‖≤B)

def input (a : ℂ →L[ℝ] ℝ) (n : ℤ) : Process (E := Noise) F μ H := by
  let v : Process (E := Noise) Fₙ μ Hₙ := BoundedFourierInput.input Fₙ μ Hₙ U hU (holder hg)
    hβ hβ₁ (nativeBound B) (bounded hb) a n
  exact processIsometry F μ r hr H v

/-- Time dilation inserts the exact Brownian Jacobian. It cancels
the inverse square root in the native coefficient pointwise. -/
theorem input_ae (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    input F μ H U hU hg hβ hβ₁ B hb a n =ᵐ[energyMeasure μ H]
      row H (pullPath r hr U) hg hβ hβ₁.le a n := by
  let v := BoundedFourierInput.input Fₙ μ Hₙ U hU (holder hg)
    hβ hβ₁ (nativeBound B) (bounded hb) a n
  filter_upwards [processIsometry_ae F μ r hr H v,
    ClockedItoAlgebra.ae_clock μ r hr H
      (BoundedFourierInput.input_ae Fₙ μ Hₙ U hU (holder hg)
        hβ hβ₁ (nativeBound B) (bounded hb) a n)] with p hp hv
  change input F μ H U hU hg hβ hβ₁ B hb a n p = _ at hp
  change v (clock r hr p.1,p.2) = _ at hv
  rw [hp,hv,BoundedFourierInput.row,smul_comm (Real.sqrt (r : ℝ)), row_scale hg hβ hβ₁.le]
  change Real.exp (min ((r : ℝ)*(p.1 : ℝ)) ((r : ℝ)*(H : ℝ))*(n : ℝ)^2) • _ = _
  rw [←mul_min_of_nonneg _ _ (show (0 : ℝ)≤r from (hr).le)]
  rfl

end SHEStochastic.ScalarUnitTorusFourierClock
