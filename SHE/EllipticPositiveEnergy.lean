module
public import SHE.HaarDamping
public import SHE.NativeCanonicalGammaEnergy
public import SHE.HaarMeasurable
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.EllipticPositiveEnergy
open MeasureTheory FiniteHaar
local instance ellipticPositive_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance ellipticPositive_sigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance ellipticPositive_borel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance ellipticPositive_second : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
variable {Ω:Type*} [MeasurableSpace Ω]
/-- True sample L2 integrability of any dependent elliptic factor pair. -/
theorem integrable (μ:Measure Ω) [IsFiniteMeasure μ] {m W:ℝ}
    (f g:Ω→EllipticField m W) (hf:Measurable f) (hg:Measurable g):
    Integrable (fun ω=>‖(f ω).val-(g ω).val‖^2) μ:=by
  have hm:Measurable (fun ω=>‖(f ω).val-(g ω).val‖^2):=
    (((measurable_subtype_coe.comp hf).sub (measurable_subtype_coe.comp hg)).norm).pow_const 2
  apply (integrable_const ((W-m)^2)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ (fun ω=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (FiniteHaar.elliptic_difference_norm_le (f ω).val (g ω).val
        (f ω).property.1 (g ω).property.1 (f ω).property.2 (g ω).property.2) 2)
end SHE.EllipticPositiveEnergy
