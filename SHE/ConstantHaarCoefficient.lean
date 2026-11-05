module
public import SHE.AdditiveHaarForcing
public import SHE.NonlinearConvolution
import all SHE.NonlinearConvolution
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
namespace SHE.ConstantHaarCoefficient
open MeasureTheory FiniteHaar LowBands NonlinearHaarIntegrand PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩

theorem field(κ:ℝ)(hκ:0<κ)(U:StateL2):
    coefficientField (fun _=>κ) measurable_const κ κ hκ (fun _=>⟨le_refl _,le_refl _⟩) U=
      AdditiveHaarForcing.constantField κ hκ:=by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [CoefficientFields.coefficient_ae (fun _=>κ) measurable_const κ
    (NonlinearHaarIntegrand.absBound hκ (fun _=>⟨le_refl _,le_refl _⟩)) U,
    AdditiveHaarForcing.constantField_ae κ hκ] with x hx hy
  exact hx.trans hy.symm


end SHE.ConstantHaarCoefficient
