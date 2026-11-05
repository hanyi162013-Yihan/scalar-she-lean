module

public import SHE.ScalarHeatBandMultipliers

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
namespace SHE.ScalarHeatSingleMultiplier
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal
local instance scalarHeatSingleMultiplier_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatSingleMultiplier_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatSingleMultiplier_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def field (a : ℝ→ℝ) (j : ℕ) (σ x : P×HeatCircle→ℝ) (p : P×HeatCircle) : ℂ:=
  (deriv (heat (σ p).toNNReal (ScalarHeatBands.band a (j+1))) (x p):ℝ)
def multiplier (a : ℝ→ℝ) (j : ℕ) (σ x : P×HeatCircle→ℝ) (p : P) : CircleL2:=
  NativeRandomRows.nativeRow (field a j σ x) p

def cap (H β : ℝ) (j : ℕ) : ℝ:=
  2*H*ScalarGaussianJetScale.constant β 0*CompactMollifier.radius (j+1)^(β-1)

theorem field_measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ)
    {σ x : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) : Measurable (field a j σ x) :=
  Complex.continuous_ofReal.measurable.comp (PolynomialGaussianDecay.derivative_measurable ha (j+1) σ x hσ hx)

theorem field_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (σ x : P×HeatCircle→ℝ) (p : P) (z : HeatCircle) :
    ‖field a j σ x (p,z)‖≤cap H β j := by
  have hs:=ScalarHeatBandJets.heated_positive_jet ha hH hβ hβ1 hh (σ (p,z)).toNNReal (j+1) 0 (x (p,z))
  simpa only [field,Complex.norm_real,Real.norm_eq_abs,Nat.zero_add,iteratedDeriv_one,Nat.cast_zero,sub_zero,cap] using hs

theorem multiplier_measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) : Measurable (multiplier a j σ x) :=
  NativeRandomRows.nativeRow_measurable (field_measurable ha j hσ hx) (field_bound ha hH hβ hβ1 hh j σ x)

theorem multiplier_ae {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ} (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x : P×HeatCircle→ℝ} (hσ : Measurable σ) (hx : Measurable x) (p : P) :
    (multiplier a j σ x p : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun z=>field a j σ x (p,z) :=
  NativeRandomRows.nativeRow_ae (field_measurable ha j hσ hx) (field_bound ha hH hβ hβ1 hh j σ x) p

/-- Sharp future-variance bound on the actual native multiplier. The
original current mean may depend on the future variance and coefficient. -/
theorem multiplier_bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ x : P×HeatCircle→ℝ} (hσm : Measurable σ) (hxm : Measurable x) (p : P)
    (hσ : ∀ᵐ z∂haarAddCircle,lo≤σ (p,z)) :
    ∀ᵐ z∂haarAddCircle,‖multiplier a j σ x p z‖≤
      (H*ScalarHeatBandEnvelope.constant β 0)*CompactMollifier.radius (j+1)^(β-1)*
        decay (CompactMollifier.radius (j+1)) lo ((3-β)/2) := by
  filter_upwards [multiplier_ae ha hH hβ hβ1 hh j hσm hxm p,hσ] with z hz hloz
  have hσz : 0<σ (p,z):=hlo.trans_le hloz
  rw [hz,field,Complex.norm_real,Real.norm_eq_abs]
  have hb:=ScalarHeatBandEnvelope.jet_bound ha hH hβ hβ1 hh (σ (p,z)).toNNReal (Real.toNNReal_pos.mpr hσz) j 0 (x (p,z))
  simp only [Nat.zero_add,iteratedDeriv_one,Nat.cast_zero,sub_zero,zero_add,Real.coe_toNNReal _ hσz.le] at hb
  have hd:=ScalarHeatGradientEnergy.decay_variance (CompactMollifier.radius_pos (j+1)) hlo
    (show 0≤(3-β)/2 by linarith) hloz
  exact hb.trans (mul_le_mul_of_nonneg_left hd
    (mul_nonneg (mul_nonneg hH (ScalarHeatBandEnvelope.constant_nonneg β 0))
      (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _)))

end SHE.ScalarHeatSingleMultiplier
