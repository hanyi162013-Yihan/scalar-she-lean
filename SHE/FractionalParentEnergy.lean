module

public import SHE.FractionalNormEnergy
public import SHE.WeightedSpatialMoments
public import SHE.ParentScoreInput
public import SHE.ParentHeatFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FractionalParentEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 OrderedHeatForests
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W]

/-- Positive old-space averaging preserves the true fractional current
input energy, without a bounded spatial representative. In particular
this also covers the newest physical rough leaf at zero heat age. -/
theorem averaged_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure W) [IsProbabilityMeasure ν]
    (K : W→ℝ) (hK : Measurable K) (hKi : Integrable K ν) (hK0 : ∀ w,0≤K w)
    (z : W→HeatCircle) (hz : Measurable z)
    (f : Ω×HeatCircle→ℝ) (hf : Measurable f)
    (hfi : Integrable (fun y=>f y^2) (μ.prod haarAddCircle))
    (χ : ℝ) (hχ : 0≤χ) (hχ1 : χ≤1) :
    let E:=∫ y,f y^2 ∂μ.prod haarAddCircle
    let G:=fun y : Ω×HeatCircle=>∫ w,K w*|f (y.1,y.2+z w)|^χ ∂ν
    Integrable (fun y=>|G y|^2) (μ.prod haarAddCircle) ∧
      (∫ y,|G y|^2 ∂μ.prod haarAddCircle)≤(∫ w,K w ∂ν)^2*E^χ := by
  intro E G
  have hE : 0≤E:=integral_nonneg (fun _=>sq_nonneg _)
  have hfrac:=FractionalNormEnergy.fractional_square f hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs,sq_abs] using hfi) hχ hχ1
  simp only [Real.norm_eq_abs,sq_abs] at hfrac
  let F : (Ω×HeatCircle)×W→ℝ:=fun y=>K y.2*|f (y.1.1,y.1.2+z y.2)|^χ
  have hFm : Measurable F:=
    (hK.comp measurable_snd).mul
      (((continuous_abs.measurable.comp hf).comp
        (measurable_fst.fst.prodMk (measurable_fst.snd.add (hz.comp measurable_snd)))).pow_const χ)
  have htranslated (w : W) :
      Integrable (fun y : Ω×HeatCircle=>|f (y.1,y.2+z w)|^((2:ℝ)*χ)) (μ.prod haarAddCircle) ∧
      (∫ y : Ω×HeatCircle,|f (y.1,y.2+z w)|^((2:ℝ)*χ) ∂μ.prod haarAddCircle)≤E^χ:=by
    let T : (Ω×HeatCircle)≃ᵐ(Ω×HeatCircle):=
      (MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.addRight (z w))
    have hT : MeasurePreserving T (μ.prod haarAddCircle) (μ.prod haarAddCircle):=
      (MeasurePreserving.id μ).prod (measurePreserving_add_right haarAddCircle (z w))
    have hi:=(hT.integrable_comp hfrac.1.aestronglyMeasurable).mpr hfrac.1
    have he:=hT.integral_comp' (fun y=>|f y|^((2:ℝ)*χ))
    refine ⟨?_,?_⟩
    · convert! hi using 1
    · exact he.le.trans hfrac.2
  have hp (y : Ω×HeatCircle) (w : W) :
      |F (y,w)|^2=(K w)^2*|f (y.1,y.2+z w)|^((2:ℝ)*χ) := by
    dsimp only [F]
    rw [abs_mul,mul_pow,sq_abs,abs_of_nonneg (rpow_nonneg (abs_nonneg _) _),
      ←Real.rpow_mul_natCast (abs_nonneg _) χ 2]
    congr 2
    ring
  have hi : ∀ᵐ w ∂ν,Integrable (fun y : Ω×HeatCircle=>|F (y,w)|^(2*1)) (μ.prod haarAddCircle):=by
    apply ae_of_all
    intro w
    simpa only [mul_one,hp] using (htranslated w).1.const_mul ((K w)^2)
  have hb : ∀ᵐ w ∂ν,(∫ y : Ω×HeatCircle,|F (y,w)|^(2*1) ∂μ.prod haarAddCircle)≤E^χ*(K w)^(2*1):=by
    apply ae_of_all
    intro w
    simp only [mul_one,hp,integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (htranslated w).2 (sq_nonneg _)).trans_eq (mul_comm _ _)
  have hh:=WeightedSpatialMoments.nonnegative_envelope (μ.prod haarAddCircle) ν F hFm
    K hK hKi hK0 1 zero_lt_one (E^χ) (rpow_nonneg hE _) hi hb
  simpa only [mul_one,one_mul,G,F,mul_comm] using hh

/-- One fractional input at any original leaf of the actual positive
parent forest costs only the finite parent-choice count, including an
unheated newest input. No spatial supremum is used. -/
theorem parent_energy (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m k : ℕ} (κ : ℝ) (hκ : 0<κ) (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t)
    (aRoot : Fin m→HeatCircle) (j : Fin (m+k))
    (f : Ω×HeatCircle→ℝ) (hf : Measurable f)
    (hfi : Integrable (fun y=>f y^2) (μ.prod haarAddCircle))
    (χ : ℝ) (hχ : 0≤χ) (hχ1 : χ≤1) :
    let G:=fun y : Ω×HeatCircle=>∫ w : Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f (y.1,y.2+values aRoot k w j)|^χ
        ∂Measure.pi (fun _=>haarAddCircle)
    Integrable (fun y=>|G y|^2) (μ.prod haarAddCircle) ∧
      (∫ y,|G y|^2 ∂μ.prod haarAddCircle)≤
        (Fintype.card (Choices m k):ℝ)^2*(∫ y,f y^2 ∂μ.prod haarAddCircle)^χ := by
  intro G
  have hKc:=(ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable (fun w : Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w))
      (Measure.pi (fun _ : Fin k=>haarAddCircle)):=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hz : Measurable (fun w : Fin k→HeatCircle=>values aRoot k w j):=
    (continuous_apply j).measurable.comp (values_continuous aRoot k).measurable
  have hh:=averaged_energy μ (Measure.pi (fun _ : Fin k=>haarAddCircle))
    (fun w=>parentDensity κ hκ k t ht (values aRoot k w)) hKc.measurable hKi
    (fun w=>parentDensity_nonneg κ hκ k t ht _) (fun w=>values aRoot k w j) hz f hf hfi χ hχ hχ1
  simpa only [G,ForestedScoreInput.parentDensity_mass] using hh

end SHE.FractionalParentEnergy
