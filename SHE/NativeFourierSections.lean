module

public import SHE.NativeFourierAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SHE.NativeFourierAverage
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance nativeFourierSections_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]

theorem scalar_coefficient_measurable (g : Ω×HeatCircle→ℂ) (hg : Measurable g) (n : ℤ) :
    Measurable (fun ω=>fourierCoeff (fun x=>g (ω,x)) n) := by
  have hm : Measurable (fun z : Ω×HeatCircle=>fourier (-n) z.2*g z):=
    (((fourier (-n)).continuous.measurable.comp measurable_snd).mul hg)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Parameter/sample Fubini for weighted Fourier realizations. Both
absolute scalar mass and genuine Hilbert integrability are retained. -/
theorem parameter_average_ae (ν : Measure A) [SFinite ν] (μ : Measure Ω) [SFinite μ]
    (v : A×Ω→CircleL2) (g : A×(Ω×HeatCircle)→ℂ)
    (hv : Integrable v (ν.prod μ)) (hg : Integrable g (ν.prod (μ.prod haarAddCircle)))
    (w : ℤ→ℂ)
    (hc : ∀ᵐ z ∂ν.prod μ,∀ n,fourierCoeff (v z) n=
      w n*fourierCoeff (fun x=>g (z.1,(z.2,x))) n) :
    ∀ᵐ ω ∂μ,∀ n,fourierCoeff (∫ a,v (a,ω) ∂ν : CircleL2) n=
      w n*fourierCoeff (fun x=>∫ a,g (a,(ω,x)) ∂ν) n := by
  have hp := (measurePreserving_prodAssoc ν μ (haarAddCircle : Measure HeatCircle)).comp
    (((Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).prod
      (MeasurePreserving.id (haarAddCircle : Measure HeatCircle))).comp
      (measurePreserving_prodAssoc μ ν (haarAddCircle : Measure HeatCircle)).symm)
  have hgs : Integrable (fun z : Ω×(A×HeatCircle)=>g (z.2.1,(z.1,z.2.2)))
      (μ.prod (ν.prod haarAddCircle)) := by
    convert! (hp.integrable_comp hg.aestronglyMeasurable).mpr hg using 1
  have hcs := (Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).quasiMeasurePreserving.ae hc
  filter_upwards [hv.swap.prod_right_ae,hgs.prod_right_ae,Measure.ae_ae_of_ae_prod hcs]
    with ω hωv hωg hωc
  exact weighted_average ν (fun a=>v (a,ω)) (fun z=>g (z.1,(ω,z.2))) hωv hωg w hωc

local instance nativeFourierSections_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeFourierSections_circleBorel : BorelSpace CircleL2:=⟨rfl⟩

/-- Separately proved parameter-section identities can be exchanged
only after their actual Fourier equality event is proved Borel. -/
theorem parameter_average_of_sections_ae (ν : Measure A) [SFinite ν] (μ : Measure Ω) [SFinite μ]
    (v : A×Ω→CircleL2) (g : A×(Ω×HeatCircle)→ℂ)
    (hvm : Measurable v) (hgm : Measurable g)
    (hv : Integrable v (ν.prod μ)) (hg : Integrable g (ν.prod (μ.prod haarAddCircle)))
    (w : ℤ→ℂ)
    (hc : ∀ᵐ a ∂ν,∀ᵐ ω ∂μ,∀ n,fourierCoeff (v (a,ω)) n=
      w n*fourierCoeff (fun x=>g (a,(ω,x))) n) :
    ∀ᵐ ω ∂μ,∀ n,fourierCoeff (∫ a,v (a,ω) ∂ν : CircleL2) n=
      w n*fourierCoeff (fun x=>∫ a,g (a,(ω,x)) ∂ν) n := by
  have hm : Measurable (fun z : (A×Ω)×HeatCircle=>g (z.1.1,(z.1.2,z.2))):=
    hgm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hs : MeasurableSet {z : A×Ω|∀ n,fourierCoeff (v z) n=
      w n*fourierCoeff (fun x=>g (z.1,(z.2,x))) n} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_eq_fun ((PhysicalProfile.fourierCoeff_continuous n).measurable.comp hvm)
      (measurable_const.mul (scalar_coefficient_measurable _ hm n))
  exact parameter_average_ae ν μ v g hv hg w ((Measure.ae_prod_iff_ae_ae hs).mpr hc)

/-- The literal scalar massive Fourier energy, defined already for L¹
fields, equals the norm of any identified weighted Hilbert realization. -/
theorem energy_of_identified (mass ρ : ℝ) (hmass : 1≤mass)
    (v : CircleL2) (g : HeatCircle→ℂ)
    (hc : ∀ n,fourierCoeff v n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff g n) :
    Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2) ∧
      (∑' n : ℤ,(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2)=‖v‖^2 := by
  have he (n : ℤ) : (mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2=
      ‖fourierCoeff v n‖^2 := by
    have hb : 0≤mass+(n:ℝ)^2:=by nlinarith [sq_nonneg (n:ℝ)]
    rw [hc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hb _),←Real.rpow_mul_natCast hb]
    norm_num only [Nat.cast_ofNat]
    rw [show (-ρ/2)*(2:ℝ) = -ρ by ring]
  refine ⟨(OneInputOperator.summable_fourier_sq v).congr (fun n=>(he n).symm),?_⟩
  rw [tsum_congr he,←OneInputOperator.norm_sq_fourier]

end SHE.NativeFourierAverage
