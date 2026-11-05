module
public import SHE.AdditivePhysicalFactor
public import SHE.ProcessEnergy
public import SHE.StoppedItoInputs
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.AdditiveHaarControl
open MeasureTheory FiniteHaar DyadicApproximation PredictableL2 AdditivePhysicalFactor
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩

/-- The actual additive-channel control in ORIGINAL Haar coordinates.
Only the fixed additive coefficient is inverted; no random noise
coefficient or reference law is changed. -/
def value (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(d:RealL2):RealHaarInput:=
  (whiteCoordinates κ hκ).symm ((Λ/Real.sqrt κ) • d)

def operator (κ:ℝ)(hκ:0<κ)(Λ:ℝ):RealL2→L[ℝ]RealHaarInput:=
  (Λ/Real.sqrt κ) • (whiteCoordinates κ hκ).symm.toLinearIsometry.toContinuousLinearMap

theorem operator_apply (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(d:RealL2):operator κ hκ Λ d=value κ hκ Λ d:=by
  simp only [operator,value,ContinuousLinearMap.smul_apply,map_smul]
  rfl

theorem norm_sq (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(d:RealL2):
    ‖value κ hκ Λ d‖^2=(Λ^2/κ)*‖d‖^2:=by
  rw [value,LinearIsometryEquiv.norm_map,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,Real.sq_sqrt hκ.le]

/-- The physical additive Haar factor sends the actual control to the
literal damping drift Lambda*d, with the correct original Haar unitary. -/
theorem reconstruct (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(d:RealL2):
    realPart (fieldFactor κ κ hκ (AdditiveHaarForcing.constantField κ hκ)
      (realInputEmbed (value κ hκ Λ d)))=Λ • d:=by
  rw [AdditivePhysicalFactor.factor_constant,value,LinearIsometryEquiv.apply_symm_apply,smul_smul]
  congr 1
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hκ)]

theorem continuous (κ:ℝ)(hκ:0<κ)(Λ:ℝ):Continuous (value κ hκ Λ):=by
  have he:value κ hκ Λ=operator κ hκ Λ:=funext (fun d=>(operator_apply κ hκ Λ d).symm)
  rw [he]
  exact (operator κ hκ Λ).continuous

variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)(H:ℝ≥0)

def process (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(D:Process (E:=RealL2) 𝓕 μ H):
    Process (E:=RealHaarInput) 𝓕 μ H:=(operator κ hκ Λ).compLp D

theorem process_ae (κ:ℝ)(hκ:0<κ)(Λ:ℝ)(D:Process (E:=RealL2) 𝓕 μ H):
    process 𝓕 μ H κ hκ Λ D=ᵐ[energyMeasure μ H] (fun p=>value κ hκ Λ (D p)):=by
  filter_upwards [ae_eq_of_ae_eq_trim ((operator κ hκ Λ).coeFn_compLp D)] with p hp
  exact hp.trans (operator_apply κ hκ Λ (D p))

/-- Exact expected squared control cost; it is the actual solution
energy times Lambda^2/kappa, not an independent moment cap. -/
theorem integral_energy (ν:Measure Ω)(κ:ℝ)(hκ:0<κ)(Λ:ℝ)(D:Ω→RealL2):
    (∫ω,‖value κ hκ Λ (D ω)‖^2 ∂ν)=(Λ^2/κ)*(∫ω,‖D ω‖^2 ∂ν):=by
  simp_rw [norm_sq]
  exact integral_const_mul _ _
end SHE.AdditiveHaarControl
