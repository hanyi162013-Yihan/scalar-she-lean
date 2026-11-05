module
public import SHE.DefectGapDensityMass
public import SHE.DefectGapKernelMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.DefectGapMixture
open Set MeasureTheory Real
open scoped NNReal ENNReal

def measure (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (Λ ρ h A0 ν:ℝ)(k:ℕ):Measure ((Fin k→ℝ)×ℝ):=
  FiniteKernelMixture.measure volume (volume.restrict (Ioc (0:ℝ) h))
    (fun d=>ENNReal.ofReal (DefectGapDensity.density P ell C k h A0 ν d))
    (DefectGapKernelMass.kernel Λ ρ k)

def cost (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (Λ ρ h A0 ν:ℝ)(k:ℕ):ℝ:=
  DefectGapDensity.mass P ell C k h A0 ν*DefectGapKernelMass.cost Λ ρ h k

theorem old_mass (P:CanonicalCovariance.ProfileParameters){ell h A0 ν:ℝ}(hell:0<ell)(hh:0<h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν):
    (∫⁻d:Fin k→ℝ,ENNReal.ofReal (DefectGapDensity.density P ell C k h A0 ν d))≤
      ENNReal.ofReal (DefectGapDensity.mass P ell C k h A0 ν):=by
  have hi:=DefectGapDensityMass.integral P hell hh C hC k hA0 hν
  rw [←ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ (DefectGapDensity.density_nonneg P hell C hC k hA0 hν))]
  exact ENNReal.ofReal_le_ofReal hi.2

/-- The actual full relative history/new-time measure has finite mass
with all assignment/rootMass factors and all original endpoint pairs. -/
theorem mass (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A0 ν:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0<h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν):
    measure P ell C Λ ρ h A0 ν k univ≤ENNReal.ofReal (cost P ell C Λ ρ h A0 ν k):=by
  have hi:=DefectGapDensityMass.integral P hell hh C hC k hA0 hν
  have hM:0≤DefectGapDensity.mass P ell C k h A0 ν:=
    (integral_nonneg (DefectGapDensity.density_nonneg P hell C hC k hA0 hν)).trans hi.2
  have he:=FiniteKernelMixture.mass volume (volume.restrict (Ioc (0:ℝ) h))
    (fun d=>ENNReal.ofReal (DefectGapDensity.density P ell C k h A0 ν d))
    (DefectGapKernelMass.kernel Λ ρ k)
    (ENNReal.measurable_ofReal.comp (DefectGapDensity.density_measurable P ell C k h A0 ν))
    (DefectGapKernelMass.measurable Λ ρ k)
    (old_mass P hell hh C hC k hA0 hν) (DefectGapKernelMass.mass hΛ hρ hρ1 hh.le k)
  rw [←ENNReal.ofReal_mul hM] at he
  exact he

theorem finite (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A0 ν:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0<h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν):
    IsFiniteMeasure (measure P ell C Λ ρ h A0 ν k):=
  ⟨(mass P hell hΛ hρ hρ1 hh C hC k hA0 hν).trans_lt ENNReal.ofReal_lt_top⟩

theorem cost_nonneg (P:CanonicalCovariance.ProfileParameters){ell Λ ρ h A0 ν:ℝ}
    (hell:0<ell)(hΛ:0<Λ)(hρ:0<ρ)(hρ1:ρ≤1)(hh:0<h)
    (C:ℕ→ℝ)(hC:∀j,0≤C j)(k:ℕ)(hA0:0≤A0)(hν:0≤ν):
    0≤cost P ell C Λ ρ h A0 ν k:=by
  have hi:=DefectGapDensityMass.integral P hell hh C hC k hA0 hν
  apply mul_nonneg ((integral_nonneg (DefectGapDensity.density_nonneg P hell C hC k hA0 hν)).trans hi.2)
  unfold DefectGapKernelMass.cost
  have hl:0≤log (2+Λ*h):=Real.log_nonneg (by nlinarith [mul_pos hΛ hh])
  positivity

end SHE.DefectGapMixture
