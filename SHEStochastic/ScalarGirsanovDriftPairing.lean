module

public import SHEStochastic.ScalarDriftNativeDirection
public import SHEStochastic.NativeFourierHeatCoordinate
public import SHEStochastic.StateNoiseCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovDriftPairing
open MeasureTheory SHE SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)

variable {H : ℝ≥0} (b : ScalarLinearGrowthDriftField.Data H)
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (c : ℝ≥0) (hc : 0<c) (hell : ∀ z,(c : ℝ)≤|g z|)

local notation "d" => ScalarLinearGrowthDriftField.divideBy b g (Continuous.measurable (HolderWith.continuous hg hβ)) c hc hell

/-- Pairing the signed Fourier noise row with the actual quotient b/g
gives exactly the ordinary Fourier drift on the original scalar state. -/
theorem fourier (t : ℝ≥0) (u : RealL2) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    inner ℝ
      (StateNoiseCovariance.row ν₂ hβ hβ₁ hg (NativeFourierHeatCoordinate.weight a n)
        (NativePhysicalState.push u))
      (NativePhysicalState.push (ScalarLinearGrowthDriftField.field d (t,u))) =
    NativeFourierHeatCoordinate.coordinate a n (ScalarLinearGrowthDriftField.field b (t,u)) := by
  let uθ := ScalarLinearGrowthDriftField.field d (t,u)
  let ub := ScalarLinearGrowthDriftField.field b (t,u)
  let k := NativeFourierHeatCoordinate.weight a n
  let s := CircleNormalization.scale (2*Real.pi) 1
  let q := StateNoiseCovariance.row ν₂ hβ hβ₁ hg k (NativePhysicalState.push u)
  rw [NativeFourierHeatCoordinate.coordinate_integral,L2.inner_def]
  have hs := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  have hθ := hs.ae (ScalarLinearGrowthDriftField.field_ae d (t,u))
  have hb := hs.ae (ScalarLinearGrowthDriftField.field_ae b (t,u))
  apply integral_congr_ae
  filter_upwards [hθ,hb,NativePhysicalState.push_ae u,NativePhysicalState.push_ae uθ,
    NativePhysicalState.push_ae ub,StateNoiseCovariance.row_ae ν₂ hβ hβ₁ hg k (NativePhysicalState.push u)]
    with x hθ hb hu hθ' hb' hq
  change uθ (s x) = b.value (min t H,(s x,u (s x)))/g (u (s x)) at hθ
  change ub (s x) = b.value (min t H,(s x,u (s x))) at hb
  change inner ℝ (q x) (NativePhysicalState.push uθ x) = k x*NativePhysicalState.push ub x
  change NativePhysicalState.push u x = u (s x) at hu
  change NativePhysicalState.push uθ x = uθ (s x) at hθ'
  change NativePhysicalState.push ub x = ub (s x) at hb'
  rw [hq,hθ',hb',hu,hθ,hb]
  change (b.value (min t H,(s x,u (s x)))/g (u (s x)))*(k x*g (u (s x))) =
    k x*b.value (min t H,(s x,u (s x)))
  have hn : g (u (s x)) ≠ 0 := by
    have hp : 0 < |g (u (s x))| := (show (0 : ℝ)<c from hc).trans_le (hell _)
    exact abs_pos.mp hp
  field_simp

end SHEStochastic.ScalarGirsanovDriftPairing
