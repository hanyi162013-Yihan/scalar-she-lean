module

public import SHE.ScalarHeatSingleMultiplier
public import SHE.ScalarHeatVarianceEnergy
public import SHE.NativePairedGammaTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace SHE.ScalarHeatPairedMultipliers
open Set MeasureTheory AddCircle Real StoppedFourier ScalarGaussianSemigroup SmoothCylinders ScalarHeatBandEnvelope
open scoped ENNReal NNReal
local instance scalarHeatPairedMultipliers_period : Fact (0<2*π):=⟨by positivity⟩
local instance scalarHeatPairedMultipliers_sigma : MeasurableSpace CircleL2:=borel _
local instance scalarHeatPairedMultipliers_borel : BorelSpace CircleL2:=⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

def six (a : ℝ→ℝ) (j : ℕ) (σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ) (p : P) : Fin 6→CircleL2:=
  ![ScalarHeatSingleMultiplier.multiplier a j σ0 z0 p,
    ScalarHeatSingleMultiplier.multiplier a j σ0 z1 p,
    ScalarHeatSingleMultiplier.multiplier a j σ1 z1 p,
    ScalarHeatSingleMultiplier.multiplier a j σ0 m0 p,
    ScalarHeatSingleMultiplier.multiplier a j σ0 m1 p,
    ScalarHeatSingleMultiplier.multiplier a j σ1 m1 p]

theorem measurable_six {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ} (hσ0 : Measurable σ0) (hσ1 : Measurable σ1)
    (hz0 : Measurable z0) (hz1 : Measurable z1) (hm0 : Measurable m0) (hm1 : Measurable m1)
    (i : Fin 6) : Measurable (fun p=>six a j σ0 σ1 z0 z1 m0 m1 p i) := by
  fin_cases i <;> simp only [six,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ0 hz0
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ0 hz1
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ1 hz1
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ0 hm0
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ0 hm1
  · exact ScalarHeatSingleMultiplier.multiplier_measurable ha hH hβ hβ1 hh j hσ1 hm1

theorem bound {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ} (hσ0 : Measurable σ0) (hσ1 : Measurable σ1)
    (hz0 : Measurable z0) (hz1 : Measurable z1) (hm0 : Measurable m0) (hm1 : Measurable m1) (p : P)
    (h0 : ∀ᵐ x∂haarAddCircle,lo≤σ0 (p,x)) (h1 : ∀ᵐ x∂haarAddCircle,lo≤σ1 (p,x)) (i : Fin 6) :
    ∀ᵐ x∂haarAddCircle,‖six a j σ0 σ1 z0 z1 m0 m1 p i x‖≤
      H*constant β 0*CompactMollifier.radius (j+1)^(β-1)*
        decay (CompactMollifier.radius (j+1)) lo ((3-β)/2) := by
  fin_cases i <;> simp only [six,Matrix.cons_val_zero,Matrix.cons_val_succ]
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ0 hz0 p h0
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ0 hz1 p h0
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ1 hz1 p h1
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ0 hm0 p h0
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ0 hm1 p h0
  · exact ScalarHeatSingleMultiplier.multiplier_bound ha hH hβ hβ1 hlo hh j hσ1 hm1 p h1

/-- Exact spatial multiplier norm for arbitrary dependent variance and
mean changes, using the actual chosen native representatives. -/
theorem difference_norm {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ τ x y : P×HeatCircle→ℝ} (hσ : Measurable σ) (hτ : Measurable τ)
    (hx : Measurable x) (hy : Measurable y) (p : P) :
    ‖ScalarHeatSingleMultiplier.multiplier a j σ x p-ScalarHeatSingleMultiplier.multiplier a j τ y p‖^2=
      ∫ z,|deriv (heat (σ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (x (p,z))-
        deriv (heat (τ (p,z)).toNNReal (ScalarHeatBands.band a (j+1))) (y (p,z))|^2 ∂haarAddCircle := by
  rw [L2_norm_sq_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (ScalarHeatSingleMultiplier.multiplier a j σ x p)
      (ScalarHeatSingleMultiplier.multiplier a j τ y p),
    ScalarHeatSingleMultiplier.multiplier_ae ha hH hβ hβ1 hh j hσ hx p,
    ScalarHeatSingleMultiplier.multiplier_ae ha hH hβ hβ1 hh j hτ hy p] with z hz h0 h1
  rw [hz,Pi.sub_apply,h0,h1,ScalarHeatSingleMultiplier.field,ScalarHeatSingleMultiplier.field,
    ←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

/-- The two root-change slots retain separate current and compatible
frozen displacements, each clipped at the actual band scale. -/
theorem root_energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ} (hσ0 : Measurable σ0)
    (hz0 : Measurable z0) (hz1 : Measurable z1) (hm0 : Measurable m0) (hm1 : Measurable m1) (p : P)
    (h0 : ∀ᵐ x∂haarAddCircle,lo≤σ0 (p,x))
    (hiZ : Integrable (fun x=>(z1 (p,x)-z0 (p,x))^2) haarAddCircle)
    (hiM : Integrable (fun x=>(m1 (p,x)-m0 (p,x))^2) haarAddCircle) :
    let b:=six a j σ0 σ1 z0 z1 m0 m1 p
    let r:=CompactMollifier.radius (j+1)
    let C:=2*H*ScalarHeatGradientDifference.constant β*r^(β-1)*decay r lo ((3-β)/2)
    ‖b 0-b 1‖^2+‖b 3-b 4‖^2≤C^2*(
      min 1 ((∫ x,(z1 (p,x)-z0 (p,x))^2 ∂haarAddCircle)/r^2)+
      min 1 ((∫ x,(m1 (p,x)-m0 (p,x))^2 ∂haarAddCircle)/r^2)) := by
  intro b r C
  have hs (f : P×HeatCircle→ℝ) (hf : Measurable f) : Measurable (fun x=>f (p,x)):=
    hf.comp (measurable_const.prodMk measurable_id)
  have hz:=ScalarHeatGradientEnergy.gradient_energy haarAddCircle ha hH hβ hβ1 hlo hh
    (fun x=>σ0 (p,x)) (fun x=>z0 (p,x)) (fun x=>z1 (p,x))
    (hs _ hσ0) (hs _ hz0) (hs _ hz1) h0 hiZ j
  have hm:=ScalarHeatGradientEnergy.gradient_energy haarAddCircle ha hH hβ hβ1 hlo hh
    (fun x=>σ0 (p,x)) (fun x=>m0 (p,x)) (fun x=>m1 (p,x))
    (hs _ hσ0) (hs _ hm0) (hs _ hm1) h0 hiM j
  have heZ:=difference_norm ha hH hβ hβ1 hh j hσ0 hσ0 hz0 hz1 p
  have heM:=difference_norm ha hH hβ hβ1 hh j hσ0 hσ0 hm0 hm1 p
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 z0 p-ScalarHeatSingleMultiplier.multiplier a j σ0 z1 p‖^2+
    ‖ScalarHeatSingleMultiplier.multiplier a j σ0 m0 p-ScalarHeatSingleMultiplier.multiplier a j σ0 m1 p‖^2≤_
  rw [heZ,heM]
  have hz':=(show (∫ x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z0 (p,x))-
      deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))|^2 ∂haarAddCircle)≤
      C^2*min 1 ((∫ x,(z1 (p,x)-z0 (p,x))^2 ∂haarAddCircle)/r^2) from by
    simpa only [C,r,abs_sub_comm] using hz.2)
  have hm':=(show (∫ x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m0 (p,x))-
      deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))|^2 ∂haarAddCircle)≤
      C^2*min 1 ((∫ x,(m1 (p,x)-m0 (p,x))^2 ∂haarAddCircle)/r^2) from by
    simpa only [C,r,abs_sub_comm] using hm.2)
  nlinarith

/-- Both changed-variance slots are controlled by the SAME true
variance difference energy, uniformly in their arbitrary dependent
current and reference means. -/
theorem variance_energy {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ)
    {σ0 σ1 z0 z1 m0 m1 : P×HeatCircle→ℝ} (hσ0 : Measurable σ0) (hσ1 : Measurable σ1)
    (hz1 : Measurable z1) (hm1 : Measurable m1) (p : P)
    (h0 : ∀ᵐ x∂haarAddCircle,lo≤σ0 (p,x)) (h1 : ∀ᵐ x∂haarAddCircle,lo≤σ1 (p,x))
    (hi : Integrable (fun x=>(σ1 (p,x)-σ0 (p,x))^2) haarAddCircle) :
    let b:=six a j σ0 σ1 z0 z1 m0 m1 p
    let r:=CompactMollifier.radius (j+1)
    let C:=(1/2:ℝ)*H*constant β 2*r^(β-3)*decay r lo ((5-β)/2)
    ‖b 1-b 2‖^2+‖b 4-b 5‖^2≤2*C^2*(∫ x,(σ1 (p,x)-σ0 (p,x))^2 ∂haarAddCircle) := by
  intro b r C
  have hs (f : P×HeatCircle→ℝ) (hf : Measurable f) : Measurable (fun x=>f (p,x)):=
    hf.comp (measurable_const.prodMk measurable_id)
  have hz:=ScalarHeatVarianceEnergy.energy haarAddCircle ha hH hβ hβ1 hlo hh j
    (fun x=>σ0 (p,x)) (fun x=>σ1 (p,x)) (fun x=>z1 (p,x))
    (hs _ hσ0) (hs _ hσ1) (hs _ hz1) h0 h1 hi
  have hm:=ScalarHeatVarianceEnergy.energy haarAddCircle ha hH hβ hβ1 hlo hh j
    (fun x=>σ0 (p,x)) (fun x=>σ1 (p,x)) (fun x=>m1 (p,x))
    (hs _ hσ0) (hs _ hσ1) (hs _ hm1) h0 h1 hi
  have heZ:=difference_norm ha hH hβ hβ1 hh j hσ0 hσ1 hz1 hz1 p
  have heM:=difference_norm ha hH hβ hβ1 hh j hσ0 hσ1 hm1 hm1 p
  change ‖ScalarHeatSingleMultiplier.multiplier a j σ0 z1 p-ScalarHeatSingleMultiplier.multiplier a j σ1 z1 p‖^2+
    ‖ScalarHeatSingleMultiplier.multiplier a j σ0 m1 p-ScalarHeatSingleMultiplier.multiplier a j σ1 m1 p‖^2≤_
  rw [heZ,heM]
  have hz':=(show (∫ x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))-
      deriv (heat (σ1 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (z1 (p,x))|^2 ∂haarAddCircle)≤
      C^2*(∫ x,(σ1 (p,x)-σ0 (p,x))^2 ∂haarAddCircle) from by
    simpa only [C,r,abs_sub_comm] using hz.2)
  have hm':=(show (∫ x,|deriv (heat (σ0 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))-
      deriv (heat (σ1 (p,x)).toNNReal (ScalarHeatBands.band a (j+1))) (m1 (p,x))|^2 ∂haarAddCircle)≤
      C^2*(∫ x,(σ1 (p,x)-σ0 (p,x))^2 ∂haarAddCircle) from by
    simpa only [C,r,abs_sub_comm] using hm.2)
  linarith

end SHE.ScalarHeatPairedMultipliers
