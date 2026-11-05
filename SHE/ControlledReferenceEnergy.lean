module

public import SHE.NativeHaarReferenceEnergy
public import SHE.ControlledProfile

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledReferenceEnergy
open Set MeasureTheory AddCircle StoppedFourier ControlledProfile ControlledResidualField
open ProfileStability ProfilePointwise
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩

theorem native_difference_norm (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) (u d : CircleL2) (θ η s : ℝ) :
    ‖native P Λ κ (((u,d),θ),s)-native P Λ κ (((u,d),η),s)‖ =
      ProfileL2.normTwo haarAddCircle (fun x => ControlledProfile.profile P Λ u d (θ,(s,x))-
        ControlledProfile.profile P Λ u d (η,(s,x))) := by
  have hh := MeasurableL2Field.real_l2_diff_norm
    (native_ae P Λ κ hκ (((u,d),θ),s)) (native_ae P Λ κ hκ (((u,d),η),s))
  simpa only [scalar,sub_sub_sub_cancel_right] using hh

/-- Sharp compatible reference energy over any physical short horizon,
for the actual TOTAL-profile-minus-additive residual Haar factors.
The initial difference is in spatial L2, with no pointwise input norm. -/
theorem native_time_energy (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ}
    (hΛ : 0≤Λ) (hκ : κ<P.lower) (u d : CircleL2) (θ η : ℝ)
    (hsmall : memoryConstant P.lower P.holder P.exponent *
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    {h : ℝ} (hh : 0<h) (hhP : h≤P.horizon) :
    let f := fun s => native P Λ κ (((u,d),θ),s)
    let g := fun s => native P Λ κ (((u,d),η),s)
    IntervalIntegrable (fun s => HaarReference.nativeEnergy (f s) (g s) (h-s)) volume 0 h ∧
      (∫ s in (0:ℝ)..h,HaarReference.nativeEnergy (f s) (g s) (h-s)) ≤
        HaarReference.rowConstant (P.lower-κ) (P.upper-κ) *
          (2*meanConstant P.lower P.holder P.exponent)^2 *
          ProfileVolterra.powerConstant ((P.exponent-1)/2)*h^(P.exponent/2)*
          (|θ-η| * ‖d‖)^2 := by
  intro f g
  have hupper : 0≤P.upper-κ := by
    have hb := ControlledProfile.profile_bounds P Λ u d (θ,(0,0))
    linarith
  have hf : Measurable f := (native_measurable P Λ κ hκ).comp
    ((measurable_const (a := ((u,d),θ))).prodMk measurable_id)
  have hg : Measurable g := (native_measurable P Λ κ hκ).comp
    ((measurable_const (a := ((u,d),η))).prodMk measurable_id)
  have hfr s := native_real_elliptic P Λ κ hκ (((u,d),θ),s)
  have hgr s := native_real_elliptic P Λ κ hκ (((u,d),η),s)
  apply HaarReference.nativeEnergy_time_bound hf hg (sub_pos.mpr hκ) hupper
    (fun s => (hfr s).mono (fun _ h => h.1)) (fun s => (hgr s).mono (fun _ h => h.1))
    (fun s => (hfr s).mono (fun _ h => h.2)) (fun s => (hgr s).mono (fun _ h => h.2))
    (by linarith [P.exponent_pos]) hh (hhP.trans P.horizon_le_one)
    (mul_nonneg (by norm_num) (meanConstant_nonneg P.lower_pos.le P.holder_nonneg))
    (by positivity : 0≤|θ-η| * ‖d‖)
  intro s hs
  dsimp only [f,g]
  rw [native_difference_norm P Λ κ hκ]
  have he := ControlledProfile.profile_l2_stability P hΛ u d θ η hsmall
    (show s∈Ioc 0 P.horizon from ⟨hs.1,hs.2.le.trans hhP⟩)
  convert he using 1 <;> ring

end SHE.ControlledReferenceEnergy
