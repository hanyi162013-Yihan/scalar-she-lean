module

public import SHE.TotalProfileParameters
public import SHE.HaarReference

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.AdditiveReference
open Set MeasureTheory AddCircle StoppedFourier GaussianProfile ProfileStability
open CanonicalCovariance CanonicalProfileL2 AdditiveProfile

local instance additiveReference_circlePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance additiveReference_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance additiveReference_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance additiveReference_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩

def constant (m : ℝ) : CircleL2 :=
  (memLp_const (μ := haarAddCircle) (p := 2) ((m^2:ℝ):ℂ)).toLp (fun _ => ((m^2:ℝ):ℂ))

theorem constant_ae (m : ℝ) : constant m =ᵐ[haarAddCircle] (fun _ => ((m^2:ℝ):ℂ)) :=
  (memLp_const (μ := haarAddCircle) (p := 2) ((m^2:ℝ):ℂ)).coeFn_toLp

def field (P : ProfileParameters) (m : ℝ) (p : CircleL2 × ℝ) : CircleL2 :=
  l2Profile (TotalProfileParameters.add P m).coefficient (m^2+P.lower) P.horizon p-constant m

theorem field_measurable (P : ProfileParameters) (m : ℝ) : Measurable (field P m) := by
  let T := TotalProfileParameters.add P m
  have hm := l2Profile_measurable T.measurable T.lower_pos T.upper_nonneg T.holder_nonneg
    T.exponent_pos T.exponent_le_one T.horizon_pos T.horizon_le_one T.lower_bound T.upper_bound T.holder_bound T.small
  exact hm.sub_const _

theorem field_ae (P : ProfileParameters) (m : ℝ) (p : CircleL2 × ℝ) :
    field P m p =ᵐ[haarAddCircle] (fun x => (residualProfile m P.coefficient P.lower P.horizon (p.1,(p.2,x)):ℂ)) := by
  let T := TotalProfileParameters.add P m
  have ht := l2Profile_ae T.measurable T.lower_pos T.upper_nonneg T.holder_nonneg
    T.exponent_pos T.exponent_le_one T.horizon_pos T.horizon_le_one T.lower_bound T.upper_bound T.holder_bound T.small p
  filter_upwards [Lp.coeFn_sub (l2Profile T.coefficient T.lower T.horizon p) (constant m),ht,constant_ae m] with x hx hy hz
  change (l2Profile T.coefficient T.lower T.horizon p-constant m) x=_
  rw [hx,Pi.sub_apply,hy,hz,← Complex.ofReal_sub]
  rfl

theorem field_real_elliptic (P : ProfileParameters) (m : ℝ) (p : CircleL2 × ℝ) :
    ∀ᵐ x ∂haarAddCircle,(field P m p x).im=0 ∧
      P.lower ≤ (field P m p x).re ∧ (field P m p x).re ≤ P.upper := by
  filter_upwards [field_ae P m p] with x hx
  rw [hx]
  exact ⟨rfl,residual_bounds P.measurable P.lower_pos P.upper_nonneg P.holder_nonneg
    P.exponent_pos P.exponent_le_one P.horizon_pos P.horizon_le_one P.lower_bound P.upper_bound
    P.holder_bound (TotalProfileParameters.add P m).small _⟩

theorem field_stability (P : ProfileParameters) (m : ℝ)
    (hsmallL2 : memoryConstant (m^2+P.lower) P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) ≤ 1/2)
    (u v : CircleL2) (r : ℝ) (hr : r ∈ Ioc 0 P.horizon) :
    ‖field P m (u,r)-field P m (v,r)‖ ≤
      2*(meanConstant (m^2+P.lower) P.holder P.exponent*‖u-v‖)*r^((P.exponent-1)/4) := by
  let T := TotalProfileParameters.add P m
  change ‖(l2Profile T.coefficient T.lower T.horizon (u,r)-constant m)-
    (l2Profile T.coefficient T.lower T.horizon (v,r)-constant m)‖ ≤ _
  rw [sub_sub_sub_cancel_right]
  exact l2Profile_stability T.measurable T.lower_pos T.upper_nonneg T.holder_nonneg T.exponent_pos
    T.exponent_le_one T.horizon_pos T.horizon_le_one T.lower_bound T.upper_bound T.holder_bound T.small hsmallL2 u v r hr

def row (P : ProfileParameters) (m : ℝ) (u v : CircleL2) (s : ℝ) : ℝ :=
  HaarReference.nativeEnergy (field P m (u,s)) (field P m (v,s)) (P.horizon-s)

def referenceConstant (P : ProfileParameters) (m : ℝ) : ℝ :=
  HaarReference.rowConstant P.lower P.upper*(2*meanConstant (m^2+P.lower) P.holder P.exponent)^2*
    ProfileVolterra.powerConstant ((P.exponent-1)/2)

/-- Actual same-Haar residual reference energy with the independent
additive variance retained in its self-consistent Gaussian profile. -/
theorem reference_energy_bound (P : ProfileParameters) (m : ℝ)
    (hsmallL2 : memoryConstant (m^2+P.lower) P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4) ≤ 1/2)
    (u v : CircleL2) :
    IntervalIntegrable (row P m u v) volume 0 P.horizon ∧
      (∫ s in (0:ℝ)..P.horizon,row P m u v s) ≤
        referenceConstant P m*P.horizon^(P.exponent/2)*‖u-v‖^2 := by
  have hm := field_measurable P m
  have hreal := field_real_elliptic P m
  have he := HaarReference.nativeEnergy_time_bound
    (f := fun s => field P m (u,s)) (g := fun s => field P m (v,s))
    (P := 2*meanConstant (m^2+P.lower) P.holder P.exponent) (D := ‖u-v‖)
    (hm.comp (measurable_const.prodMk measurable_id)) (hm.comp (measurable_const.prodMk measurable_id))
    P.lower_pos P.upper_nonneg
    (fun s => (hreal (u,s)).mono (fun _ hx => hx.1))
    (fun s => (hreal (v,s)).mono (fun _ hx => hx.1))
    (fun s => (hreal (u,s)).mono (fun _ hx => hx.2))
    (fun s => (hreal (v,s)).mono (fun _ hx => hx.2))
    (by linarith [P.exponent_pos] : -1 < P.exponent) P.horizon_pos P.horizon_le_one
    (mul_nonneg (by norm_num) (meanConstant_nonneg (add_nonneg (sq_nonneg m) P.lower_pos.le) P.holder_nonneg))
    (norm_nonneg _) (fun s hs => by
      have hb := field_stability P m hsmallL2 u v s ⟨hs.1,hs.2.le⟩
      convert hb using 1; ring)
  exact ⟨he.1,he.2⟩

end SHE.AdditiveReference
