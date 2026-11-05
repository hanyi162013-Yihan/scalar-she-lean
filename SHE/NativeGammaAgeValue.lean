module
public import SHE.NativeGammaAgeMeasure
public import SHE.NativeCanonicalGammaSharp
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeGammaAgeValue
open Set MeasureTheory Real StoppedFourier
open scoped NNReal ENNReal
variable {Ω:Type*} [MeasurableSpace Ω]
/-- The reflected current lies in the ORIGINAL strict stochastic
window, so no clipped-clock branch survives on the age interval. -/
theorem window (v b:ℝ≥0) {τ:ℝ} (hτ:τ∈Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (ω:Ω):
    (((b:ℝ)-τ).toNNReal,ω)∈NativeGammaClock.window v b:=by
  have hq:0≤(b:ℝ)-τ:=by linarith [hτ.2,v.coe_nonneg]
  constructor
  · exact_mod_cast (show (v:ℝ)<(((b:ℝ)-τ).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hq];linarith [hτ.2])
  · exact_mod_cast (show (((b:ℝ)-τ).toNNReal:ℝ)<(b:ℝ) by
      rw [Real.coe_toNNReal _ hq];linarith [hτ.1])

theorem age (v b:ℝ≥0) {τ:ℝ} (hτ:τ∈Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (ω:Ω):
    NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω)=τ:=by
  rw [NativeGammaClock.age,if_pos (window v b hτ ω),
    Real.coe_toNNReal _ (by linarith [hτ.2,v.coe_nonneg]:0≤(b:ℝ)-τ)]
  ring

/-- Exact canonical polynomial Gaussian-band envelope in future age. -/
theorem sharp (P:CanonicalCovariance.ProfileParameters) (v b:ℝ≥0) (A β:ℝ) (j:ℕ)
    {τ:ℝ} (hτ:τ∈Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (ω:Ω):
    NativeCanonicalGammaSharp.sharp (v:=v) (b:=b) (P:=P) A β j (((b:ℝ)-τ).toNNReal,ω)=
      A*ScalarHeatBandEnvelope.constant β 0*CompactMollifier.radius (j+1)^(β-1)*
        ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1))
          (ProfileVariance.lowerConstant*P.lower*sqrt τ) ((3-β)/2):=by
  unfold NativeCanonicalGammaSharp.sharp NativeCanonicalGammaSharp.lower
  rw [age v b hτ ω,Real.sqrt_eq_rpow]

/-- The physical/unit-circle time normalization is retained exactly
when the two factor-trace powers are transported to future age. -/
theorem clock_power {τ:ℝ} (hτ:0≤τ) (p:ℝ):
    (NativeHeatSpan.clock τ)^p=(4*π^2)^(-p)*τ^p:=by
  rw [NativeHeatSpan.clock,Real.div_rpow hτ (by positivity),Real.rpow_neg (by positivity:0≤4*π^2)]
  ring
end SHE.NativeGammaAgeValue
