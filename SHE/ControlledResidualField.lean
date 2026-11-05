module

public import SHE.ControlledProfileFamilies
public import SHE.MeasurableL2Field
public import SHE.CircleNormalization
public import SHE.HaarHeatIntegrand

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ControlledResidualField
open Set MeasureTheory AddCircle StoppedFourier ControlledProfile MeasurableL2Field
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩

abbrev Parameters := (Inputs × ℝ) × ℝ

/-- Actual residual of the controlled TOTAL Gaussian profile. -/
def scalar (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (p : Parameters × HeatCircle) : ℂ :=
  (ControlledProfile.profile P Λ p.1.1.1.1 p.1.1.1.2 (p.1.1.2,(p.1.2,p.2))-κ : ℝ)

theorem scalar_measurable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) :
    Measurable (scalar P Λ κ) := by
  have hmap : Measurable (fun p : Parameters × HeatCircle => (p.1.1,(p.1.2,p.2))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  exact Complex.measurable_ofReal.comp
    (((ControlledProfile.profile_joint_measurable P Λ).comp hmap).sub_const κ)

theorem scalar_memLp (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) (p : Parameters) :
    MemLp (fun x => scalar P Λ κ (p,x)) 2 haarAddCircle := by
  apply MemLp.of_bound
    ((scalar_measurable P Λ κ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (P.upper-κ)
  exact Filter.Eventually.of_forall (fun x => by
    have hb := ControlledProfile.profile_bounds P Λ p.1.1.1 p.1.1.2 (p.1.2,(p.2,x))
    change ‖((ControlledProfile.profile P Λ p.1.1.1 p.1.1.2 (p.1.2,(p.2,x))-κ : ℝ):ℂ)‖≤_
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith :
      0≤ControlledProfile.profile P Λ p.1.1.1 p.1.1.2 (p.1.2,(p.2,x))-κ)]
    linarith)

def native (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) : Parameters → CircleL2 :=
  realizeL2 (ν := haarAddCircle) (scalar P Λ κ)

theorem native_ae (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) (p : Parameters) :
    native P Λ κ p =ᵐ[haarAddCircle] fun x => scalar P Λ κ (p,x) :=
  realizeL2_ae (scalar P Λ κ) (scalar_memLp P Λ κ hκ) p

theorem native_measurable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) : Measurable (native P Λ κ) :=
  realizeL2_measurable (scalar_measurable P Λ κ) (scalar_memLp P Λ κ hκ)

theorem native_real_elliptic (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) (p : Parameters) :
    ∀ᵐ x ∂haarAddCircle, (native P Λ κ p x).im=0 ∧
      P.lower-κ≤(native P Λ κ p x).re ∧ (native P Λ κ p x).re≤P.upper-κ := by
  filter_upwards [native_ae P Λ κ hκ p] with x hx
  rw [hx]
  have hb := ControlledProfile.profile_bounds P Λ p.1.1.1 p.1.1.2 (p.1.2,(p.2,x))
  exact ⟨rfl,sub_le_sub_right hb.1 κ,sub_le_sub_right hb.2 κ⟩

/-- Literal unit-circle residual coefficient for the SAME native Haar
factor, with the exact clock/spatial normalization transported. -/
def field (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : κ<P.lower)
    (p : Parameters) : FiniteHaar.EllipticField (P.lower-κ) (P.upper-κ) := by
  let f := CircleNormalization.push.symm (native P Λ κ p)
  have hf := native_real_elliptic P Λ κ hκ p
  exact ⟨f,
    CircleNormalization.push_symm_ae_property _ (fun z => z.im=0) (hf.mono (fun _ h => h.1)),
    CircleNormalization.push_symm_ae_property _ (fun z => P.lower-κ≤z.re ∧ z.re≤P.upper-κ)
      (hf.mono (fun _ h => h.2))⟩

theorem field_measurable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) : Measurable (field P Λ κ hκ) := by
  apply Measurable.subtype_mk
  exact CircleNormalization.push.symm.continuous.measurable.comp (native_measurable P Λ κ hκ)

theorem push_field (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ)
    (hκ : κ<P.lower) (p : Parameters) :
    CircleNormalization.push (field P Λ κ hκ p).val=native P Λ κ p :=
  CircleNormalization.push.apply_symm_apply _

end SHE.ControlledResidualField
