module

public import SHE.AdditiveHaarForcing
public import SHE.HaarPhysicalAnalysis

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.AdditivePhysicalFactor
open MeasureTheory AddCircle CircleHeat FiniteHaar DyadicApproximation AdditiveHaarForcing
open scoped ENNReal
local instance additivePhysicalFactor_periodPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def whiteCoordinates (κ : ℝ) (hκ : 0 < κ) : RealHaarInput ≃ₗᵢ[ℝ] RealL2 :=
  (fieldRealInnovation κ κ hκ (constantField κ hκ)).symm

theorem root_constant (κ : ℝ) (hκ : 0 < κ) (v : CircleL2) :
    CircleMultiplier.rootEquivalence (constantField κ hκ).1 κ κ hκ
      ((constantField κ hκ).2.2.mono (fun _ h => h.1))
      ((constantField κ hκ).2.2.mono (fun _ h => h.2)) v=(Real.sqrt κ) • v := by
  let f := constantField κ hκ
  let hu := f.2.2.mono (fun _ h => h.2)
  change CircleMultiplier.operator (CircleMultiplier.rootCoefficient f.1 κ hu) (Real.sqrt κ)
    (CircleMultiplier.rootCoefficient_norm_bound f.1 κ hu) v= _
  apply Lp.ext
  filter_upwards [CircleMultiplier.operator_ae (CircleMultiplier.rootCoefficient f.1 κ hu) (Real.sqrt κ)
    (CircleMultiplier.rootCoefficient_norm_bound f.1 κ hu) v,
    CircleMultiplier.rootCoefficient_ae f.1 κ hu,constantField_ae κ hκ,
    Lp.coeFn_smul (Real.sqrt κ) v] with y hop hr hf hs
  rw [hop,hr,hf,hs]
  simp only [Complex.ofReal_re]
  rfl

theorem realPart_realEmbed (v : RealL2) : realPart (realEmbed v)=v :=
  realCircleIdentification.symm_apply_apply v

theorem realPart_smul (r : ℝ) (v : CircleL2) : realPart (r • v)=r • realPart v := by
  change (Complex.reCLM.compLpL 2 haarAddCircle) (r • v)=r • (Complex.reCLM.compLpL 2 haarAddCircle) v
  exact map_smul _ _ _

/-- The actual constant Haar factor is sqrtκ times a fixed genuine
physical unitary. Hence κ=m₀² is precisely a common additive m₀ noise
after a coefficient-independent ordinary noise rotation. -/
theorem factor_constant (κ : ℝ) (hκ : 0 < κ) (x : RealHaarInput) :
    realPart (fieldFactor κ κ hκ (constantField κ hκ) (realInputEmbed x))=
      Real.sqrt κ • whiteCoordinates κ hκ x := by
  let J := fieldRealInnovation κ κ hκ (constantField κ hκ)
  have hh := real_factor_realInnovation hκ (constantField κ hκ) (J.symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at hh
  rw [root_constant,realPart_smul,realPart_realEmbed] at hh
  exact hh

/-- The identical factor identity on analysis rows, for arbitrary real
physical L² tests and therefore for every genuine heat observation. -/
theorem analysis_constant (κ : ℝ) (hκ : 0 < κ) (v : RealL2) :
    realInputPart (factorAnalysis (constantField κ hκ).1 κ κ hκ
      (constantField κ hκ).2.1 (constantField κ hκ).2.2 (realEmbed v))=
      Real.sqrt κ • (whiteCoordinates κ hκ).symm v := by
  rw [realFactorAnalysis_innovation hκ (constantField κ hκ),root_constant,realPart_smul,realPart_realEmbed,map_smul]
  rfl

theorem factor_amplitude (m : ℝ) (hm : 0 < m) (x : RealHaarInput) :
    realPart (fieldFactor (m^2) (m^2) (sq_pos_of_pos hm)
      (constantField (m^2) (sq_pos_of_pos hm)) (realInputEmbed x))=
      m • whiteCoordinates (m^2) (sq_pos_of_pos hm) x := by
  rw [factor_constant,Real.sqrt_sq hm.le]

end SHE.AdditivePhysicalFactor
