module
public import SHE.DefectGapMixture
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.DefectGapMixtureIntegral
open Set MeasureTheory Real
open scoped NNReal ENNReal BigOperators

theorem realKernel_nonneg {Λ ρ τ:ℝ}(hΛ:0≤Λ)(k:ℕ)(d:Fin k→ℝ)(hτ:0≤τ):
    0≤DefectGapKernelMass.realKernel Λ ρ k d τ:=
  Finset.sum_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>
    DefectCombinedTime.nonneg hΛ (DefectGapKernelMass.offsets_nonneg k d i)
      (DefectGapKernelMass.offsets_nonneg k d j) hτ))

/-- The complete positive relative mixture is exactly the original
gap density times the all-pair current kernel. This supplies genuine
product L1 before any signed Fubini operation. -/
theorem integral (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A0 ν:ℝ}
    (hell:0<ell)(hΛ:0≤Λ)(C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)
    (hA0:0≤A0)(hν:0≤ν)(J:((Fin k→ℝ)×ℝ)→ℝ)
    (hi:Integrable J (DefectGapMixture.measure P ell C Λ ρ h A0 ν k)):
    Integrable (fun p:(Fin k→ℝ)×ℝ=>
      DefectGapDensity.density P ell C k h A0 ν p.1*
        DefectGapKernelMass.realKernel Λ ρ k p.1 p.2*J p)
      ((volume:Measure (Fin k→ℝ)).prod (volume.restrict (Ioc (0:ℝ) h))) ∧
    (∫p,J p ∂DefectGapMixture.measure P ell C Λ ρ h A0 ν k)=
      ∫d:Fin k→ℝ,DefectGapDensity.density P ell C k h A0 ν d*
        (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ*J (d,τ)
          ∂volume.restrict (Ioc (0:ℝ) h)):=by
  let D:=DefectGapDensity.density P ell C k h A0 ν
  let K:=DefectGapKernelMass.realKernel Λ ρ k
  let m:Measure ((Fin k→ℝ)×ℝ):=volume.prod (volume.restrict (Ioc (0:ℝ) h))
  let W:((Fin k→ℝ)×ℝ)→ℝ≥0∞:=fun p=>ENNReal.ofReal (D p.1)*ENNReal.ofReal (K p.1 p.2)
  have hW:Measurable W:=
    ((ENNReal.measurable_ofReal.comp (DefectGapDensity.density_measurable P ell C k h A0 ν)).comp
      measurable_fst).mul (DefectGapKernelMass.measurable Λ ρ k)
  have hWf:∀ᵐp∂m,W p<∞:=ae_of_all _ (fun p=>ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have he:∀ᵐp∂m,(W p).toReal=D p.1*K p.1 p.2:=by
    have ht:∀ᵐp:(Fin k→ℝ)×ℝ∂m,p.2∈Ioc (0:ℝ) h:=
      (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).mpr
        (ae_of_all _ (fun _=>ae_restrict_mem measurableSet_Ioc))
    filter_upwards [ht] with p hp
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal
      (DefectGapDensity.density_nonneg P hell C hC k hA0 hν p.1),
      ENNReal.toReal_ofReal (realKernel_nonneg hΛ k p.1 hp.1.le)]
  have hJ:Integrable J (m.withDensity W):=hi
  have hs:Integrable (fun p=>(W p).toReal •J p) m:=
    (integrable_withDensity_iff_integrable_smul₀' hW.aemeasurable hWf).mp hJ
  have hw:Integrable (fun p=>D p.1*K p.1 p.2*J p) m:=by
    apply hs.congr
    filter_upwards [he] with p hp
    rw [hp,smul_eq_mul]
  refine ⟨hw,?_⟩
  change (∫p,J p ∂m.withDensity W)=_
  rw [integral_withDensity_eq_integral_toReal_smul hW hWf]
  calc
    _=∫p,D p.1*K p.1 p.2*J p ∂m:=integral_congr_ae (he.mono (fun p hp=>by rw [hp,smul_eq_mul]))
    _=∫d:Fin k→ℝ,∫τ:ℝ,D d*K d τ*J (d,τ)
        ∂volume.restrict (Ioc (0:ℝ) h):=integral_prod _ hw
    _=_:=by
      apply integral_congr_ae
      filter_upwards with d
      simpa only [mul_assoc] using integral_const_mul (D d) (fun τ=>K d τ*J (d,τ))
end SHE.DefectGapMixtureIntegral
