module
public import SHE.NativeGammaAgeValue
public import SHE.NativeJointGammaSharp
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeGammaAgeNormalize
open Set MeasureTheory StoppedFourier
open scoped NNReal ENNReal
variable {Ω:Type*} [MeasurableSpace Ω]
/-- Normalize the physical future-age clock under its ORIGINAL iterated
age/sample integral. Only the terminal Lebesgue endpoint is discarded;
no joint-in-past stochastic versions or new measurability premise occur. -/
theorem integral (μ:Measure Ω) (v b:ℝ≥0) (F:(ℝ≥0×Ω)→ℝ→ℝ):
    (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal
      (F (((b:ℝ)-τ).toNNReal,ω) (NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω))) ∂μ)=
    (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (F (((b:ℝ)-τ).toNNReal,ω) τ) ∂μ):=by
  have hm:∀ᵐτ∂volume.restrict (Ioc (0:ℝ) ((b:ℝ)-(v:ℝ))),τ∈Ioo (0:ℝ) ((b:ℝ)-(v:ℝ)):=by
    rw [←restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  apply lintegral_congr_ae
  filter_upwards [hm] with τ hτ
  apply lintegral_congr
  intro ω
  rw [NativeGammaAgeValue.age v b hτ ω]

/-- The literal JOINT sharp envelope has exactly the same physical-age
formula as its canonical lower-variance envelope. This identifies only
the common envelope, not the distinct corrected and joint currents. -/
theorem sharp (P:CanonicalCovariance.ProfileParameters) (v b:ℝ≥0) (A β:ℝ) (j:ℕ)
    {τ:ℝ} (hτ:τ∈Ioo (0:ℝ) ((b:ℝ)-(v:ℝ))) (ω:Ω):
    NativeJointGammaSharp.sharp (v:=v) (b:=b) (P:=P) A β j (((b:ℝ)-τ).toNNReal,ω)=
      A*ScalarHeatBandEnvelope.constant β 0*CompactMollifier.radius (j+1)^(β-1)*
        ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1))
          (ProfileVariance.lowerConstant*P.lower*Real.sqrt τ) ((3-β)/2):=by
  exact NativeGammaAgeValue.sharp P v b A β j hτ ω

/-- Exact normalization for each of the four actual native row budgets. -/
theorem row (μ:Measure Ω) (v b:ℝ≥0) (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ) (ρ:ℝ) (i l:Fin 6):
    (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal
      ((NativeGammaClock.age v b (((b:ℝ)-τ).toNNReal,ω))^(ρ-1/2)*
        ‖NativeRandomRows.nativeRow (g i) (((b:ℝ)-τ).toNNReal,ω)-
          NativeRandomRows.nativeRow (g l) (((b:ℝ)-τ).toNNReal,ω)‖^2) ∂μ)=
    (∫⁻τ in Ioc (0:ℝ) ((b:ℝ)-(v:ℝ)),∫⁻ω,ENNReal.ofReal (τ^(ρ-1/2)*
      ‖NativeRandomRows.nativeRow (g i) (((b:ℝ)-τ).toNNReal,ω)-
        NativeRandomRows.nativeRow (g l) (((b:ℝ)-τ).toNNReal,ω)‖^2) ∂μ):=
  integral μ v b (fun p τ=>τ^(ρ-1/2)*‖NativeRandomRows.nativeRow (g i) p-NativeRandomRows.nativeRow (g l) p‖^2)
end SHE.NativeGammaAgeNormalize
