module

public import SHE.ScalarHeatBandBernstein
public import SHE.LowBands

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.ScalarHeatLowBands
open MeasureTheory Real SmoothCylinders ScalarHeatBands ScalarHeatBandBernstein LowBands
open scoped NNReal ENNReal
local instance lowBands_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {a:ℝ→ℝ} (ha:BoundedSmooth a) {B H β:ℝ}
variable (hB:∀x,|a x|≤B) (hH:0≤H) (hβ:0≤β) (hβ1:β≤1)
variable (hh:∀x y,|a x-a y|≤H*|x-y|^β)

def lip (j:ℕ):ℝ≥0:=⟨amplitude B H β 1*(((2:ℝ)^j)^(1-β)),
  mul_nonneg (amplitude_nonneg hH 1) (rpow_nonneg (by positivity) _)⟩

include ha hB hβ hβ1 hh in
/-- The actual Gaussian heat bands have a Bernstein Lipschitz bound
independent of every unsmoothed derivative. The first band is included. -/
theorem real_lipschitz (j:ℕ):LipschitzWith (lip (B:=B) (β:=β) hH j) (band a j):=by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((band_boundedSmooth ha j).smooth.differentiable (by norm_num))
  intro x
  have hx:=all_jets ha hB hH hβ hβ1 hh 1 j 1 (by norm_num) x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one] at hx
  have he:((amplitude B H β 1*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^(1:ℕ))=
      (lip (B:=B) (β:=β) hH j:ℝ):=by
    change (amplitude B H β 1*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^(1:ℕ)=
      amplitude B H β 1*((2:ℝ)^j)^(1-β)
    rw [pow_one,mul_assoc]
    congr 1
    calc
      _=((2:ℝ)^j)^(-β)*((2:ℝ)^j)^(1:ℝ):=by rw [Real.rpow_one]
      _=((2:ℝ)^j)^(-β+1):=(Real.rpow_add (pow_pos (by norm_num : (0:ℝ)<2) j) (-β) 1).symm
      _=_:=by congr 1;ring
  rw [he] at hx
  exact_mod_cast hx

include ha hB hβ hβ1 hh in
theorem complex_lipschitz (j:ℕ):LipschitzWith (lip (B:=B) (β:=β) hH j)
    (fun x=>(band a j x:ℂ)):=by
  have hr:=real_lipschitz ha hB hH hβ hβ1 hh j
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  change ‖(band a j x:ℂ)-(band a j y:ℂ)‖≤_
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  simpa only [Real.dist_eq] using hr.dist_le_mul x y

def comparison (N:ℕ) (U V:StateL2):CircleHeat.CircleL2:=
  LowBands.comparison (fun j x=>(band a j x:ℂ)) (lip (B:=B) (β:=β) hH)
    (complex_lipschitz ha hB hH hβ hβ1 hh) (Finset.range (N+1)) U V

/-- All direct original low-band hypotheses are instantiated by the
SAME real Gaussian heat bands used in the complete Gamma estimates. -/
theorem comparison_norm (hβlt:β<1) (N:ℕ) (U V:StateL2):
    ‖comparison ha hB hH hβ hβ1 hh N U V‖≤
      (amplitude B H β 1*LowBands.lowBandConstant β)*(((2:ℝ)^N)^(1-β))*‖U-V‖:=by
  exact LowBands.dyadic_comparison_norm hβlt (amplitude_nonneg hH 1)
    (fun j x=>(band a j x:ℂ)) (lip (B:=B) (β:=β) hH)
    (complex_lipschitz ha hB hH hβ hβ1 hh) (fun _=>le_rfl) N U V

theorem comparison_negative_norm {κ Λ ρ:ℝ} (hΛ:0<Λ) (hρ:0≤ρ)
    (hβlt:β<1) (N:ℕ) (U V:StateL2):
    Real.sqrt (StepInput.negativeEnergy κ Λ ρ (comparison ha hB hH hβ hβ1 hh N U V))≤
      ((amplitude B H β 1*LowBands.lowBandConstant β)*Λ^(-ρ/2))*
        (((2:ℝ)^N)^(1-β))*‖U-V‖:=by
  exact LowBands.dyadic_comparison_negative_norm hΛ hρ hβlt (amplitude_nonneg hH 1)
    (fun j x=>(band a j x:ℂ)) (lip (B:=B) (β:=β) hH)
    (complex_lipschitz ha hB hH hβ hβ1 hh) (fun _=>le_rfl) N U V

/-- The checked low block is literally the finite scalar heat cutoff
at the original endpoints, including the first band. -/
theorem comparison_ae (N:ℕ) (U V:StateL2):
    comparison ha hB hH hβ hβ1 hh N U V=ᵐ[AddCircle.haarAddCircle]
      fun x=>(smooth a N (U x)-smooth a N (V x):ℂ):=by
  let A:ℕ→CircleHeat.CircleL2:=fun j=>
    LowBands.composeBand (fun x=>(band a j x:ℂ)) (complex_lipschitz ha hB hH hβ hβ1 hh j) U-
      LowBands.composeBand (fun x=>(band a j x:ℂ)) (complex_lipschitz ha hB hH hβ hβ1 hh j) V
  have hb(j:ℕ):A j=ᵐ[AddCircle.haarAddCircle]
      fun x=>(band a j (U x):ℂ)-(band a j (V x):ℂ):=
    LowBands.composeBand_difference_ae _ _ U V
  have hs:=Lp.coeFn_fun_finsetSum (Finset.range (N+1)) A
  filter_upwards [hs,ae_all_iff.mpr hb] with x hx hj
  change (∑j∈Finset.range (N+1),A j) x=_
  rw [hx]
  calc
    _=∑j∈Finset.range (N+1),((band a j (U x)-band a j (V x):ℝ):ℂ):=by
      apply Finset.sum_congr rfl
      intro j _
      rw [hj j,Complex.ofReal_sub]
    _=((∑j∈Finset.range (N+1),(band a j (U x)-band a j (V x)):ℝ):ℂ):=by push_cast;rfl
    _=_:=by rw [Finset.sum_sub_distrib,sum_band,sum_band,Complex.ofReal_sub]

end SHE.ScalarHeatLowBands
