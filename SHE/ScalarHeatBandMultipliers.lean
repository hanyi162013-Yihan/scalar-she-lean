module

public import SHE.ScalarHeatGradientEnergy
public import SHE.NativeOutputTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.ScalarHeatBandMultipliers
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier NativeHeatObservation ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
local instance scalarHeatBandMultipliers_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatBandMultipliers_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatBandMultipliers_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def field (a : ℝ→ℝ) (j : ℕ) (σ x y : P×HeatCircle→ℝ) (p : P×HeatCircle) : ℂ:=
  (deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (y p)-
    deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p):ℝ)

def multiplier (a : ℝ→ℝ) (j : ℕ) (σ x y : P×HeatCircle→ℝ) (p : P) : CircleL2:=
  NativeRandomRows.nativeRow (field a j σ x y) p

def cap (H β : ℝ) (j : ℕ) : ℝ:=
  4*H*ScalarGaussianJetScale.constant β 0*CompactMollifier.radius (j+1)^(β-1)

theorem field_measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) (hy : Measurable y) :
    Measurable (field a j σ x y) :=
  Complex.continuous_ofReal.measurable.comp
    ((PolynomialGaussianDecay.derivative_measurable ha (j+1) σ y hσ hy).sub
      (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hσ hx))

theorem field_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (σ x y : P×HeatCircle→ℝ) (p : P) (z : HeatCircle) :
    ‖field a j σ x y (p,z)‖≤cap H β j := by
  have hfirst:=ScalarHeatBandJets.heated_positive_jet ha hH hβ hβ1 hh (σ (p,z)).toNNReal (j+1) 0 (y (p,z))
  have hsecond:=ScalarHeatBandJets.heated_positive_jet ha hH hβ hβ1 hh (σ (p,z)).toNNReal (j+1) 0 (x (p,z))
  simp only [Nat.zero_add,iteratedDeriv_one,Nat.cast_zero,sub_zero] at hfirst hsecond
  rw [field,Complex.norm_real,Real.norm_eq_abs]
  calc
    _≤|deriv (heat (σ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (y (p,z))|+
        |deriv (heat (σ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (x (p,z))|:=abs_sub _ _
    _≤2*H*ScalarGaussianJetScale.constant β 0*CompactMollifier.radius (j+1)^(β-1)+
        2*H*ScalarGaussianJetScale.constant β 0*CompactMollifier.radius (j+1)^(β-1):=add_le_add hfirst hsecond
    _=cap H β j:=by dsimp only [cap]; ring

theorem multiplier_measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) (hy : Measurable y) :
    Measurable (multiplier a j σ x y) :=
  NativeRandomRows.nativeRow_measurable (field_measurable ha j hσ hx hy) (field_bound ha hH hβ hβ1 hh j σ x y)

theorem multiplier_ae {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) (hy : Measurable y) (p : P) :
    (multiplier a j σ x y p : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun z=>field a j σ x y (p,z) :=
  NativeRandomRows.nativeRow_ae (field_measurable ha j hσ hx hy) (field_bound ha hH hβ hβ1 hh j σ x y) p

theorem multiplier_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) (hy : Measurable y) (p : P) :
    ∀ᵐ z∂haarAddCircle,‖multiplier a j σ x y p z‖≤cap H β j := by
  filter_upwards [multiplier_ae ha hH hβ hβ1 hh j hσ hx hy p] with z hz
  rw [hz]
  exact field_bound ha hH hβ hβ1 hh j σ x y p z

/-- The actual native L² multiplier of the second complete-Gamma term
has the clipped state energy; its representative and joint Borel map
were constructed above from the literal scalar field. -/
theorem multiplier_energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x y : P×HeatCircle→ℝ} (hσm : Measurable σ) (hxm : Measurable x) (hym : Measurable y) (p : P)
    (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z))
    (hi : Integrable (fun z=>(y (p,z)-x (p,z))^2) haarAddCircle) :
    ‖multiplier a j σ x y p‖^2≤
      ((2*H*ScalarHeatGradientDifference.constant β)*CompactMollifier.radius (j+1)^(β-1)*
        decay (CompactMollifier.radius (j+1)) lo ((3-β)/2))^2*
        min 1 ((∫ z,(y (p,z)-x (p,z))^2 ∂haarAddCircle)/CompactMollifier.radius (j+1)^2) := by
  have hm (f : P×HeatCircle→ℝ) (hf : Measurable f) : Measurable (fun z=>f (p,z)):=
    hf.comp (measurable_const.prodMk measurable_id)
  have he:=ScalarHeatGradientEnergy.gradient_energy haarAddCircle ha hH hβ hβ1 hlo hh
    (fun z=>σ (p,z)) (fun z=>x (p,z)) (fun z=>y (p,z)) (hm σ hσm) (hm x hxm) (hm y hym) hσ hi j
  rw [L2_norm_sq_eq_integral]
  have heq : (∫ z,‖multiplier a j σ x y p z‖^2 ∂haarAddCircle)=
      ∫ z,|deriv (heat (σ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (y (p,z))-
        deriv (heat (σ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (x (p,z))|^2 ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [multiplier_ae ha hH hβ hβ1 hh j hσm hxm hym p] with z hz
    rw [hz,field,Complex.norm_real,Real.norm_eq_abs]
  rw [heq]
  exact he.2

end SHE.ScalarHeatBandMultipliers
