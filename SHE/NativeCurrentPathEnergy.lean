module

public import SHE.NativeHeatFunctionalEnergy
public import SHE.JointInterpolationFields
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeCurrentPathEnergy
open Set MeasureTheory Real NativeHeatObservation DyadicApproximation StoppedFourier AddCircle
open scoped ENNReal
local instance nativeCurrentPath_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeCurrentPath_realMeasurable : MeasurableSpace RealL2 := borel _
local instance nativeCurrentPath_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]

def direction (D : ℝ×Ω→RealL2) (Λ s τ : ℝ) (z : (ℝ×Ω)×HeatCircle) : ℝ :=
  functional τ z.2 (D (z.1.1+s,z.1.2))-
    (exp (-Λ*s)*(1-exp (-Λ*τ)))*functional (s+τ) z.2 (D z.1)

theorem direction_measurable (D : ℝ×Ω→RealL2) (hD : Measurable D) (Λ s τ : ℝ) :
    Measurable (direction D Λ s τ) := by
  have ht : Measurable (fun z : (ℝ×Ω)×HeatCircle=>(z.1.1+s,z.1.2)):=
    (measurable_fst.fst.add_const s).prodMk measurable_fst.snd
  have h0:=functional_joint_measurable.comp
    ((hD.comp ht).prodMk ((measurable_const (a:=τ)).prodMk measurable_snd))
  have h1:=functional_joint_measurable.comp
    ((hD.comp measurable_fst).prodMk ((measurable_const (a:=s+τ)).prodMk measurable_snd))
  exact h0.sub (h1.const_mul _)

/-- The literal corrected physical root has its true global path energy.
The moving-past translation is integrated exactly, without any pointwise
current-state cap or independence assumption. -/
theorem energy (D : ℝ×Ω→RealL2) (hD : Measurable D)
    (hi : Integrable (fun z=>‖D z‖^2) ((volume : Measure ℝ).prod μ))
    {Λ s τ : ℝ} (hΛ : 0≤Λ) (hs : 0≤s) (hτ : 0<τ) :
    Integrable (fun z=>direction D Λ s τ z^2)
      (((volume : Measure ℝ).prod μ).prod haarAddCircle) ∧
      (∫z,direction D Λ s τ z^2 ∂(((volume : Measure ℝ).prod μ).prod haarAddCircle))≤
        4*∫z,‖D z‖^2 ∂((volume : Measure ℝ).prod μ) := by
  let e : ℝ×Ω ≃ᵐ ℝ×Ω := (MeasurableEquiv.addRight s).prodCongr (MeasurableEquiv.refl Ω)
  have hp : MeasurePreserving e ((volume : Measure ℝ).prod μ) ((volume : Measure ℝ).prod μ) :=
    (measurePreserving_add_right volume s).prod (MeasurePreserving.id μ)
  have his : Integrable (fun z=>‖D (z.1+s,z.2)‖^2) ((volume : Measure ℝ).prod μ) :=
    (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have he : (∫z,‖D (z.1+s,z.2)‖^2 ∂((volume : Measure ℝ).prod μ))=
      (∫z,‖D z‖^2 ∂((volume : Measure ℝ).prod μ)) := by
    exact hp.integral_comp' (fun z=>‖D z‖^2)
  have hbound:= (his.const_mul 2).add (hi.const_mul 2)
  have hm:Measurable (fun z=>direction D Λ s τ z^2):=(direction_measurable D hD Λ s τ).pow_const 2
  have hsec (z : ℝ×Ω) := NativeHeatFunctionalEnergy.current_energy hΛ hs hτ (D (z.1+s,z.2)) (D z)
  have hI : Integrable (fun z=>direction D Λ s τ z^2)
      (((volume : Measure ℝ).prod μ).prod haarAddCircle) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun z=>(hsec z).1),?_⟩
    apply hbound.mono'
      (hm.norm.stronglyMeasurable.integral_prod_right.measurable.aestronglyMeasurable)
    filter_upwards [] with z
    have hn : (∫x,‖direction D Λ s τ (z,x)^2‖ ∂haarAddCircle)=
      (∫x,direction D Λ s τ (z,x)^2 ∂haarAddCircle):=by
      apply integral_congr_ae
      exact ae_of_all _ (fun _=>Real.norm_of_nonneg (sq_nonneg _))
    rw [Real.norm_of_nonneg (integral_nonneg (fun _=>norm_nonneg _)),hn]
    exact (hsec z).2.2
  refine ⟨hI,?_⟩
  rw [integral_prod _ hI]
  calc
    _≤∫z,2*‖D (z.1+s,z.2)‖^2+2*‖D z‖^2 ∂((volume : Measure ℝ).prod μ):=
      integral_mono hI.integral_prod_left hbound (fun z=>(hsec z).2.2)
    _=4*∫z,‖D z‖^2 ∂((volume : Measure ℝ).prod μ):=by
      rw [integral_add (his.const_mul 2) (hi.const_mul 2),integral_const_mul,integral_const_mul,he]
      ring

end SHE.NativeCurrentPathEnergy
