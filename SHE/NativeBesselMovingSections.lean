module
public import SHE.NativeBesselFieldAE
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBesselMovingSections
open Set MeasureTheory StoppedFourier
open scoped ENNReal
local instance nativeBesselMovingSections_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeBesselMovingSections_sigma : MeasurableSpace CircleL2:=borel _
local instance nativeBesselMovingSections_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeBesselMovingSections_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {P Ω:Type*}[MeasurableSpace P][MeasurableSpace Ω]
variable (ν:Measure P)(μ:Measure Ω)[SFinite ν][SFinite μ]

def field (Y:(P×HeatCircle)×Ω→ℝ)(z:(P×Ω)×HeatCircle):ℂ:=Y ((z.1.1,z.2),z.1.2)
theorem field_measurable (Y:(P×HeatCircle)×Ω→ℝ)(hY:Measurable Y):Measurable (field Y):=
  Complex.continuous_ofReal.measurable.comp
    (hY.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd))

/-- Exact original past/root/sample reordering of the positive spatial
square mass, before choosing its native Hilbert representative. -/
theorem square_mass (Y:(P×HeatCircle)×Ω→ℝ)(hY:Measurable Y):
    (∫⁻p,MeasurableL2FieldAE.squareMass AddCircle.haarAddCircle (field Y) p ∂ν.prod μ)=
      (∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle):=by
  have hm:=((field_measurable Y hY).norm.pow_const 2).ennreal_ofReal
  have hmY:Measurable (fun z:(P×HeatCircle)×Ω=>ENNReal.ofReal (|Y z|^2)):=by
    simpa only [Real.norm_eq_abs] using ((hY.norm.pow_const 2).ennreal_ofReal)
  rw [lintegral_prod _ (MeasurableL2FieldAE.mass_measurable AddCircle.haarAddCircle (field Y)
    (field_measurable Y hY)).aemeasurable]
  rw [lintegral_prod _ (hmY.lintegral_prod_right').aemeasurable]
  apply lintegral_congr
  intro p
  dsimp only [MeasurableL2FieldAE.squareMass]
  rw [lintegral_lintegral_swap]
  · congr 1
    funext x
    apply lintegral_congr
    intro ω
    simp only [field,Complex.norm_real,Real.norm_eq_abs]
  · exact (hm.comp (((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).aemeasurable

variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)

include hΛ hρ in
/-- A jointly Borel scalar family with finite ORIGINAL square energy
has one Borel native Bessel realization. Any original fixed-past
physical output with its proved coefficients is its actual section. -/
theorem exists_identified (Y:(P×HeatCircle)×Ω→ℝ)(hY:Measurable Y)
    (hE:(∫⁻z,∫⁻ω,ENNReal.ofReal (|Y (z,ω)|^2) ∂μ ∂ν.prod AddCircle.haarAddCircle)<∞)
    (Z:P→Ω→CircleL2)
    (hZ:∀ᵐp∂ν,∀ᵐω∂μ,∀l:ℤ,fourierCoeff (Z p ω) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x:HeatCircle=>(Y ((p,x),ω):ℂ)) l):
    ∃G:P×Ω→CircleL2,Measurable G ∧
      (∀ᵐp∂ν,(fun ω=>G (p,ω))=ᵐ[μ] Z p) ∧
      ∀ᵐz∂ν.prod μ,
        Summable (fun l:ℤ=>(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x:HeatCircle=>(Y ((z.1,x),z.2):ℂ)) l‖^2) ∧
        (∑'l:ℤ,(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x:HeatCircle=>(Y ((z.1,x),z.2):ℂ)) l‖^2)=‖G z‖^2:=by
  let F:=field Y
  have hF:Measurable F:=field_measurable Y hY
  have hfinite:(∫⁻p,MeasurableL2FieldAE.squareMass AddCircle.haarAddCircle F p ∂ν.prod μ)<∞:=
    (square_mass ν μ Y hY).trans_lt hE
  let G:=NativeBesselFieldAE.value Λ ρ hΛ hρ F
  have hG:Measurable G:=NativeBesselFieldAE.measurable Λ ρ hΛ hρ F hF
  have hg:=MeasurableL2FieldAE.good_ae AddCircle.haarAddCircle (ν.prod μ) F hF hfinite
  refine ⟨G,hG,?_,NativeBesselFieldAE.energy_ae Λ ρ hΛ hρ (ν.prod μ) F hF hfinite⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hg,hZ] with p hp hz
  filter_upwards [hp,hz] with ω hω hz
  apply (_root_.fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext l
  simp only [fourierBasis_repr,hz]
  simpa only [G,F,field] using NativeBesselFieldAE.coefficients Λ ρ hΛ hρ F hF (p,ω) hω l
end SHE.NativeBesselMovingSections
