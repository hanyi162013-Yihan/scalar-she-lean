module

public import SHE.ControlledReferenceEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledReferenceEnergy
open Set MeasureTheory AddCircle StoppedFourier ControlledProfile ControlledResidualField
open ProfileStability ProfilePointwise
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩

def kernelEnergy (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : κ<P.lower)
    (u d : CircleL2) (θ η h s : ℝ) : ℝ :=
  ‖NativeHeatObservation.kernel (P.lower-κ) (P.upper-κ) (sub_pos.mpr hκ)
      (h-s,field P Λ κ hκ (((u,d),θ),s))-
    NativeHeatObservation.kernel (P.lower-κ) (P.upper-κ) (sub_pos.mpr hκ)
      (h-s,field P Λ κ hκ (((u,d),η),s))‖^2

/-- The actual REAL Hilbert noise-column energy is integrable and has
the sharp compatible Gaussian reference gain. Both factors use the same
countable Haar coordinates, and the additive channel cancels exactly. -/
theorem kernel_time_energy (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ}
    (hΛ : 0≤Λ) (hκ : κ<P.lower) (u d : CircleL2) (θ η : ℝ)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    {h : ℝ} (hh : 0<h) (hhP : h≤P.horizon) :
    IntervalIntegrable (kernelEnergy P Λ κ hκ u d θ η h) volume 0 h ∧
      (∫ s in (0:ℝ)..h,kernelEnergy P Λ κ hκ u d θ η h s) ≤
        HaarReference.rowConstant (P.lower-κ) (P.upper-κ) *
          (2*meanConstant P.lower P.holder P.exponent)^2 *
          ProfileVolterra.powerConstant ((P.exponent-1)/2)*h^(P.exponent/2)*
          (|θ-η| * ‖d‖)^2 := by
  have hb := native_time_energy P hΛ hκ u d θ η hsmall hh hhP
  have he : kernelEnergy P Λ κ hκ u d θ η h =ᵐ[volume.restrict (uIoc (0:ℝ) h)]
      fun s => HaarReference.nativeEnergy (native P Λ κ (((u,d),θ),s))
        (native P Λ κ (((u,d),η),s)) (h-s) := by
    rw [uIoc_of_le hh.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne h)] with s hs hsh
    have hage : 0<h-s := sub_pos.mpr (lt_of_le_of_ne hs.2 hsh)
    unfold kernelEnergy
    rw [NativeHaarReferenceEnergy.kernel_difference_energy _ hage,
      push_field,push_field]
  refine ⟨hb.1.congr_ae he.symm,?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict he]
  exact hb.2

end SHE.ControlledReferenceEnergy
