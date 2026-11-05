module
public import SHE.NativeGammaAgeBound
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.GammaPositiveIntegralSplit
open MeasureTheory
open scoped ENNReal
variable {X:Type*} [MeasurableSpace X]
/-- Exact positive-integral splitting of the six-term Gamma budget.
This does not replace any stochastic or analytic term by a premise;
it records the finite-sum step used after the actual same-J isometry. -/
theorem split (ν:Measure X) (s f d0 d1 d2 d3:X→ℝ)
    (hs:Measurable s) (hf:Measurable f) (h0:Measurable d0) (h1:Measurable d1)
    (h2:Measurable d2) (h3:Measurable d3) {K:ℝ} (hK:0≤K):
    (∫⁻x,ENNReal.ofReal (6*(s x+f x+K*(d0 x+d1 x+d2 x+d3 x))) ∂ν)≤
      6*((∫⁻x,ENNReal.ofReal (s x) ∂ν)+(∫⁻x,ENNReal.ofReal (f x) ∂ν)+
        ENNReal.ofReal K*((∫⁻x,ENNReal.ofReal (d0 x) ∂ν)+(∫⁻x,ENNReal.ofReal (d1 x) ∂ν)+
          (∫⁻x,ENNReal.ofReal (d2 x) ∂ν)+(∫⁻x,ENNReal.ofReal (d3 x) ∂ν))):=by
  have hsf:Measurable (fun x=>ENNReal.ofReal (s x)+ENNReal.ofReal (f x)):=hs.ennreal_ofReal.add hf.ennreal_ofReal
  have h01:Measurable (fun x=>ENNReal.ofReal (d0 x)+ENNReal.ofReal (d1 x)):=h0.ennreal_ofReal.add h1.ennreal_ofReal
  have h012:Measurable (fun x=>ENNReal.ofReal (d0 x)+ENNReal.ofReal (d1 x)+ENNReal.ofReal (d2 x)):=h01.add h2.ennreal_ofReal
  calc
    _≤∫⁻x,(6:ℝ≥0∞)*(ENNReal.ofReal (s x)+ENNReal.ofReal (f x)+
        ENNReal.ofReal K*(ENNReal.ofReal (d0 x)+ENNReal.ofReal (d1 x)+
          ENNReal.ofReal (d2 x)+ENNReal.ofReal (d3 x))) ∂ν:=by
      apply lintegral_mono
      intro x
      dsimp only
      rw [ENNReal.ofReal_mul (by norm_num:0≤(6:ℝ))]
      norm_num only [ENNReal.ofReal_ofNat]
      gcongr
      apply ENNReal.ofReal_add_le.trans
      apply add_le_add ENNReal.ofReal_add_le
      rw [ENNReal.ofReal_mul hK]
      gcongr
      exact ENNReal.ofReal_add_le.trans (add_le_add
        (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)) le_rfl)
    _=_:=by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_add_left hsf,
        lintegral_add_left hs.ennreal_ofReal,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left h012,
        lintegral_add_left h01,
        lintegral_add_left h0.ennreal_ofReal]
end SHE.GammaPositiveIntegralSplit
