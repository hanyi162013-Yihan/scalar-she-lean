module

public import SHE.NativeFourierSections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace SHE.NativeFourierAverage
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance negativeThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

def scalarEnergy (mass ρ : ℝ) (g : HeatCircle→ℂ) : ℝ:=
  ∑' n : ℤ,(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2

theorem scalarEnergy_nonneg (mass ρ : ℝ) (hmass : 0≤mass) (g : HeatCircle→ℂ) : 0≤scalarEnergy mass ρ g :=
  tsum_nonneg (fun _=>mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))

theorem besselHalf_norm_sq_mass (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) (v : CircleL2) :
    ‖OneInputOperator.besselHalf mass ρ hmass hρ v‖^2≤mass^(-ρ)*‖v‖^2 := by
  have he (n : ℤ) : ‖fourierCoeff (OneInputOperator.besselHalf mass ρ hmass hρ v) n‖^2=
      (mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff v n‖^2 := by
    have hb : 0≤mass+(n:ℝ)^2:=by nlinarith [sq_nonneg (n:ℝ)]
    rw [OneInputOperator.besselHalf_fourierCoeff,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hb _),←Real.rpow_mul_natCast hb]
    norm_num only [Nat.cast_ofNat]
    rw [show (-ρ/2)*(2:ℝ) = -ρ by ring]
  rw [OneInputOperator.norm_sq_fourier,OneInputOperator.norm_sq_fourier,
    ←(OneInputOperator.summable_fourier_sq v).tsum_mul_left]
  apply Summable.tsum_le_tsum _ (OneInputOperator.summable_fourier_sq _)
    ((OneInputOperator.summable_fourier_sq v).mul_left (mass^(-ρ)))
  intro n
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by linarith : 0<mass)
      (le_add_of_nonneg_right (sq_nonneg (n:ℝ))) (neg_nonpos.mpr hρ)) (sq_nonneg _)

/-- The literal scalar three-leg identity transfers to massive output
energy even when the mean leg itself is known only in L¹. -/
theorem three_leg_energy (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (C V B : CircleL2) (m g : HeatCircle→ℂ)
    (hm : Integrable m haarAddCircle)
    (hsplit : g=ᵐ[haarAddCircle] fun x=>C x+m x+B x)
    (hmean : ∀ n,fourierCoeff V n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff m n) :
    Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2) ∧
      (∑' n : ℤ,(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2)≤
        3*(mass^(-ρ)*(‖C‖^2+‖B‖^2)+‖V‖^2) := by
  let Q:=OneInputOperator.besselHalf mass ρ hmass hρ
  let W:=Q C+V+Q B
  have hiC : Integrable (C : HeatCircle→ℂ) haarAddCircle:=
    (Lp.memLp C).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hiB : Integrable (B : HeatCircle→ℂ) haarAddCircle:=
    (Lp.memLp B).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hcoeff (n : ℤ) : fourierCoeff W n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff g n := by
    rw [←coefficient_apply,show W=Q C+V+Q B from rfl,map_add,map_add]
    simp only [coefficient_apply,Q,OneInputOperator.besselHalf_fourierCoeff,hmean]
    rw [congrFun (fourierCoeff_congr_ae hsplit) n]
    change _= _*fourierCoeff ((C : HeatCircle→ℂ)+m+(B : HeatCircle→ℂ)) n
    rw [fourierCoeff.add (hiC.add hm) hiB,fourierCoeff.add hiC hm]
    simp only [Pi.add_apply]
    ring
  have he:=energy_of_identified mass ρ hmass W g hcoeff
  refine ⟨he.1,he.2.le.trans ?_⟩
  have hn : ‖W‖≤‖Q C‖+‖V‖+‖Q B‖:= by
    calc
      ‖W‖≤‖Q C+V‖+‖Q B‖:=norm_add_le _ _
      _≤‖Q C‖+‖V‖+‖Q B‖:=by gcongr;exact norm_add_le _ _
  have hc:=besselHalf_norm_sq_mass mass ρ hmass hρ C
  have hb:=besselHalf_norm_sq_mass mass ρ hmass hρ B
  have hs₁:=sq_nonneg (‖Q C‖-‖V‖)
  have hs₂:=sq_nonneg (‖Q C‖-‖Q B‖)
  have hs₃:=sq_nonneg (‖V‖-‖Q B‖)
  have hsq:=pow_le_pow_left₀ (norm_nonneg W) hn 2
  nlinarith

theorem scalar_three_leg_energy (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (c b m g : HeatCircle→ℂ) (hc : MemLp c 2 haarAddCircle) (hb : MemLp b 2 haarAddCircle)
    (hm : Integrable m haarAddCircle) (V : CircleL2)
    (hsplit : g=ᵐ[haarAddCircle] fun x=>c x+m x+b x)
    (hmean : ∀ n,fourierCoeff V n=
      (((mass+(n:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff m n) :
    Summable (fun n : ℤ=>(mass+(n:ℝ)^2)^(-ρ)*‖fourierCoeff g n‖^2) ∧
      scalarEnergy mass ρ g≤
        3*(mass^(-ρ)*((∫ x,‖c x‖^2 ∂haarAddCircle)+(∫ x,‖b x‖^2 ∂haarAddCircle))+‖V‖^2) := by
  let C:=hc.toLp c
  let B:=hb.toLp b
  have hs : g=ᵐ[haarAddCircle] fun x=>C x+m x+B x := by
    filter_upwards [hsplit,hc.coeFn_toLp,hb.coeFn_toLp] with x hx hcx hbx
    change g x=C x+m x+B x
    rw [hcx,hbx]
    exact hx
  have he:=three_leg_energy mass ρ hmass hρ C V B m g hm hs hmean
  have hCnorm : ‖C‖^2=∫ x,‖c x‖^2 ∂haarAddCircle := by
    rw [StoppedFourier.L2_norm_sq_eq_integral]
    exact integral_congr_ae (hc.coeFn_toLp.mono (fun x hx=>congrArg (fun z : ℂ=>‖z‖^2) hx))
  have hBnorm : ‖B‖^2=∫ x,‖b x‖^2 ∂haarAddCircle := by
    rw [StoppedFourier.L2_norm_sq_eq_integral]
    exact integral_congr_ae (hb.coeFn_toLp.mono (fun x hx=>congrArg (fun z : ℂ=>‖z‖^2) hx))
  simpa only [scalarEnergy,hCnorm,hBnorm] using he

end SHE.NativeFourierAverage
