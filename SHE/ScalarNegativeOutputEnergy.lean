module

public import SHE.NegativeThreeLeg
public import SHE.NativeNegativeRealization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.NativeFourierAverage
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- A genuine output L2 field has the full massive negative-energy gain.
This cannot be inferred just from a scalar root-averaged bound. -/
theorem scalar_negative_energy (mass ρ:ℝ) (hmass:1≤mass) (hρ:0≤ρ)
    (g:HeatCircle→ℂ) (hg:MemLp g 2 haarAddCircle):
    Summable (fun n:ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2) ∧
      scalarEnergy mass ρ g≤mass^(-ρ)*(∫x,‖g x‖^2 ∂haarAddCircle):=by
  let G:CircleL2:=hg.toLp g
  let Q:=OneInputOperator.besselHalf mass ρ hmass hρ G
  have hcoeff(n:ℤ):fourierCoeff Q n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff g n:=by
    rw [OneInputOperator.besselHalf_fourierCoeff]
    exact congrArg (fun z:ℂ=>(((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*z)
      (congrFun (fourierCoeff_congr_ae hg.coeFn_toLp) n)
  have he:=energy_of_identified mass ρ hmass Q g hcoeff
  have hG:‖G‖^2=∫x,‖g x‖^2 ∂haarAddCircle:=by
    rw [L2_norm_sq_eq_integral]
    exact integral_congr_ae (hg.coeFn_toLp.mono (fun x hx=>congrArg (fun z:ℂ=>‖z‖^2) hx))
  refine ⟨he.1,he.2.le.trans ?_⟩
  simpa only [hG] using besselHalf_norm_sq_mass mass ρ hmass hρ G

variable {X:Type*} [MeasurableSpace X]

theorem scalarEnergy_measurable (mass ρ:ℝ) (g:X×HeatCircle→ℂ) (hg:Measurable g):
    Measurable (fun z=>scalarEnergy mass ρ (fun x=>g (z,x))):=by
  exact Measurable.tsum (fun n=>(measurable_const.mul
    ((scalar_coefficient_measurable g hg n).norm.pow_const 2)))

/-- Literal parameter-space/native-output L2 implies integrated massive
Fourier energy, with the exact mass^(-rho) factor. All fibre L2 membership
is derived from the original product integrability. -/
theorem scalar_negative_product_energy (ν:Measure X) [SFinite ν]
    (mass ρ:ℝ) (hmass:1≤mass) (hρ:0≤ρ)
    (g:X×HeatCircle→ℂ) (hg:Measurable g)
    (hi:Integrable (fun z=>‖g z‖^2) (ν.prod haarAddCircle)):
    Integrable (fun z=>scalarEnergy mass ρ (fun x=>g (z,x))) ν ∧
      (∫z,scalarEnergy mass ρ (fun x=>g (z,x)) ∂ν)≤
        mass^(-ρ)*(∫z,‖g z‖^2 ∂ν.prod haarAddCircle):=by
  have hm:=scalarEnergy_measurable mass ρ g hg
  have hs:∀ᵐz∂ν,scalarEnergy mass ρ (fun x=>g (z,x))≤
      mass^(-ρ)*(∫x,‖g (z,x)‖^2 ∂haarAddCircle):=by
    filter_upwards [hi.prod_right_ae] with z hz
    have hgz:MemLp (fun x=>g (z,x)) 2 haarAddCircle:=
      (memLp_two_iff_integrable_sq_norm ((hg.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)).mpr hz
    exact (scalar_negative_energy mass ρ hmass hρ _ hgz).2
  have hdom:Integrable (fun z=>mass^(-ρ)*(∫x,‖g (z,x)‖^2 ∂haarAddCircle)) ν:=
    hi.integral_prod_left.const_mul _
  have hiE:Integrable (fun z=>scalarEnergy mass ρ (fun x=>g (z,x))) ν:=hdom.mono' hm.aestronglyMeasurable
    (hs.mono (fun z hz=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (scalarEnergy_nonneg mass ρ (by linarith) _)]
      exact hz))
  refine ⟨hiE,(integral_mono_ae hiE hdom hs).trans_eq ?_⟩
  rw [integral_const_mul]
  congr 1
  exact (integral_prod _ hi).symm

/-- The same bound is realized by an actual native Hilbert output,
not merely by a formal weighted Fourier sum. -/
theorem negative_realization_product_energy (ν:Measure X) [SFinite ν]
    (mass ρ:ℝ) (hmass:1≤mass) (hρ:0≤ρ)
    (g:X×HeatCircle→ℂ) (hg:Measurable g)
    (hi:Integrable (fun z=>‖g z‖^2) (ν.prod haarAddCircle)):
    Integrable (fun z=>‖NativeNegativeRealization.value mass ρ g z‖^2) ν ∧
      (∫z,‖NativeNegativeRealization.value mass ρ g z‖^2 ∂ν)≤
        mass^(-ρ)*(∫z,‖g z‖^2 ∂ν.prod haarAddCircle):=by
  simpa only [NativeNegativeRealization.value_norm_sq mass ρ hmass] using
    scalar_negative_product_energy ν mass ρ hmass hρ g hg hi

end SHE.NativeFourierAverage
