module
public import SHE.NativeGammaAgeValue
public import SHE.HeatBandCausalEnergy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.NativeGammaBandDensity
open Set MeasureTheory Real ScalarHeatBandEnvelope
open scoped NNReal ENNReal

/-- The literal canonical Gaussian-band envelope is bounded by the
proved causal polynomial kernel, with its exact sharp band scale. -/
theorem envelope {A β c τ:ℝ} (hβ:β≤1) (hc:0<c) (hτ:0<τ) (j:ℕ):
    (A*constant β 0*CompactMollifier.radius (j+1)^(β-1)*
      decay (CompactMollifier.radius (j+1)) (c*sqrt τ) ((3-β)/2))^2*τ^(-(1/2:ℝ))≤
      HeatBandCausalEnergy.density A β c j τ:=by
  let r:=CompactMollifier.radius (j+1)
  have hr:0<r:=CompactMollifier.radius_pos (j+1)
  have hd:=PolynomialGaussianDecay.decay_sq_bound hr hc hτ
    (by linarith:0≤(3-β)/2) (le_refl (c*sqrt τ))
  have hp:(r^(β-1))^2=r^(2*β-2):=by
    rw [←Real.rpow_two,←Real.rpow_mul hr.le]
    congr 1
    ring
  have hfac:0≤(A*constant β 0)^2*r^(2*β-2)*τ^(-(1/2:ℝ)):=by positivity
  have he:=mul_le_mul_of_nonneg_left hd hfac
  convert he using 1 <;>
    simp only [HeatBandCausalEnergy.density,PolynomialGaussianTime.kernel,
      show (1/2:ℝ)-1=-(1/2:ℝ) by ring,mul_pow,hp,r] <;> ring

/-- Exact native-clock normalization of the signed-factor trace;
the physical/unit-circle clock contributes only a fixed scalar. -/
theorem signed_kernel {A β c τ:ℝ} (hβ:β≤1) (hc:0<c) (hτ:0<τ) (j:ℕ):
    ENNReal.ofReal ((A*constant β 0*CompactMollifier.radius (j+1)^(β-1)*
      decay (CompactMollifier.radius (j+1)) (c*sqrt τ) ((3-β)/2))^2*
        (NativeHeatSpan.clock τ)^(-(1/2:ℝ)))≤
      ENNReal.ofReal ((4*π^2)^(1/2:ℝ))*HeatBandCausalEnergy.kernel A β c j τ:=by
  rw [NativeGammaAgeValue.clock_power hτ.le,neg_neg]
  rw [HeatBandCausalEnergy.kernel,indicator_of_mem (show τ∈Ioi (0:ℝ) from hτ)]
  rw [←ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he:=mul_le_mul_of_nonneg_left (envelope (A:=A) hβ hc hτ j)
    (Real.rpow_nonneg (by positivity:0≤4*π^2) (1/2:ℝ))
  convert he using 1 <;> ring
end SHE.NativeGammaBandDensity
