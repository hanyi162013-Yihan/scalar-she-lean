module

public import SHE.CellTranslation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.SmoothCellSobolev
open Finset Set MeasureTheory AddCircle CircleHeat CircleFractional FiniteHaar ArcFourier CellTranslation
open scoped ENNReal
local instance smoothCellSobolev_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def kernel (N ρ z : ℝ) : ℝ := N^(1+2*ρ)*CyclicStep.fractionalKernel ρ (N*z)
def fractionalConstant (ρ : ℝ) : ℝ := 1/(1-2*ρ)+1/(2*ρ)

theorem kernel_integrable {N ρ : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    Integrable (kernel N ρ) :=
  ((integrable_comp_mul_left_iff (CyclicStep.fractionalKernel ρ) hN.ne').mpr
    (CyclicStep.integrable_fractionalKernel hρ hρhalf)).const_mul _

theorem kernel_integral {N ρ : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hρhalf : ρ < 1/2) :
    (∫ z : ℝ, kernel N ρ z) = N^(2*ρ)*fractionalConstant ρ := by
  unfold kernel
  rw [integral_const_mul,Measure.integral_comp_mul_left,CyclicStep.integral_fractionalKernel hρ hρhalf,
    smul_eq_mul,abs_of_pos (inv_pos.mpr hN)]
  rw [← Real.rpow_neg_one N]
  calc
    _ = (N^(1+2*ρ)*N^(-1:ℝ))*fractionalConstant ρ := by unfold fractionalConstant; ring
    _ = _ := by rw [← Real.rpow_add hN]; congr 2; ring

theorem kernel_nonneg {N ρ : ℝ} (hN : 0 ≤ N) (z : ℝ) : 0 ≤ kernel N ρ z :=
  mul_nonneg (Real.rpow_nonneg hN _) (CyclicStep.fractionalKernel_nonneg ρ (N*z))

theorem kernel_eq {N z ρ : ℝ} (hN : 0 < N) (hz : 0 < z) :
    kernel N ρ z = min 1 (N*z)*z^(-1-2*ρ) := by
  have hNz := mul_pos hN hz
  have hrescale : N^(1+2*ρ)*(N*z)^(-1-2*ρ) = z^(-1-2*ρ) := by
    rw [Real.mul_rpow hN.le hz.le,← mul_assoc,← Real.rpow_add hN]
    simp only [show 1+2*ρ+(-1-2*ρ) = 0 by ring,Real.rpow_zero,one_mul]
  unfold kernel CyclicStep.fractionalKernel
  by_cases hs : N*z ≤ 1
  · rw [Set.indicator_of_mem (show N*z ∈ Ioc (0:ℝ) 1 from ⟨hNz,hs⟩),
      Set.indicator_of_notMem (show N*z ∉ Ioi (1:ℝ) from not_lt.mpr hs),add_zero,min_eq_right hs]
    have he : (N*z)^(-2*ρ) = (N*z)*(N*z)^(-1-2*ρ) := by
      calc
        _ = (N*z)^(1+(-1-2*ρ)) := by congr 1; ring
        _ = (N*z)^(1:ℝ)*(N*z)^(-1-2*ρ) := Real.rpow_add hNz _ _
        _ = _ := by rw [Real.rpow_one]
    rw [he]
    calc
      _ = (N*z)*(N^(1+2*ρ)*(N*z)^(-1-2*ρ)) := by ring
      _ = _ := by rw [hrescale]
  · rw [Set.indicator_of_notMem (show N*z ∉ Ioc (0:ℝ) 1 from fun h => hs h.2),
      Set.indicator_of_mem (show N*z ∈ Ioi (1:ℝ) from lt_of_not_ge hs),zero_add,
      min_eq_left (le_of_not_ge hs),one_mul]
    exact hrescale

theorem measurable_translation_energy (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) :
    Measurable (circleTranslationEnergy (cut n x u)) := by
  have hm : Measurable (cut n x u) := u.continuous.measurable.indicator (measurableSet_cellSet n x)
  have hp : Measurable (fun p : ℝ × AddCircle (1:ℝ) => ‖cut n x u (p.2+(p.1 : AddCircle (1:ℝ)))-cut n x u p.2‖^2) :=
    ((hm.comp (by fun_prop)).sub (hm.comp measurable_snd)).norm.pow_const 2
  exact hp.stronglyMeasurable.integral_prod_right'.measurable

/-- A genuine local smooth-cell Sobolev estimate. Only amplitude and
Lipschitz bounds inside the literal cell are used; no global derivative
or Sobolev extension hypothesis is supplied. -/
theorem cut_gagliardo_bound {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (A L : ℝ)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ A)
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w) :
    IntegrableOn (fun z : ℝ => circleTranslationEnergy (cut n x u) z*z^(-1-2*ρ)) (Ioi 0) ∧
      circleFractionalSq ρ (cut n x u) ≤
        fractionalConstant ρ*(((2^n:ℕ):ℝ))^(2*ρ)*
          (L^2*(((2^n:ℕ):ℝ))⁻¹^3+4*A^2*(((2^n:ℕ):ℝ))⁻¹) := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  let C : ℝ := L^2*N⁻¹^3+4*A^2*N⁻¹
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := ((kernel_integrable hN hρ hρhalf).const_mul C).integrableOn (s := Ioi (0:ℝ))
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ => circleTranslationEnergy (cut n x u) z*z^(-1-2*ρ)) (volume.restrict (Ioi 0)) :=
    ((measurable_translation_energy n x u).mul (by fun_prop)).aestronglyMeasurable
  have hpoint {z : ℝ} (hz : 0 < z) :
      circleTranslationEnergy (cut n x u) z*z^(-1-2*ρ) ≤ C*kernel N ρ z := by
    rw [kernel_eq hN hz]
    exact (mul_le_mul_of_nonneg_right (cut_translation_bound n x u A L hA hL hu hlip hz.le)
      (Real.rpow_nonneg hz.le (-1-2*ρ))).trans_eq (by dsimp only [C,N]; ring)
  have hfinite : IntegrableOn (fun z : ℝ => circleTranslationEnergy (cut n x u) z*z^(-1-2*ρ)) (Ioi 0) := by
    apply hi.mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have ht0 : 0 ≤ circleTranslationEnergy (cut n x u) z := integral_nonneg (fun _ => sq_nonneg _)
    rw [Real.norm_of_nonneg (mul_nonneg ht0 (Real.rpow_nonneg hz.le _))]
    exact hpoint hz
  refine ⟨hfinite,?_⟩
  have hb := integral_mono_ae hfinite hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact hpoint hz)
  have ht := setIntegral_le_integral (s := Ioi (0:ℝ)) ((kernel_integrable hN hρ hρhalf).const_mul C)
    (ae_of_all _ (fun z => mul_nonneg hC (kernel_nonneg hN.le z)))
  change (∫ z : ℝ in Ioi 0, circleTranslationEnergy (cut n x u) z*z^(-1-2*ρ)) ≤ _
  apply (hb.trans ht).trans_eq
  rw [integral_const_mul,kernel_integral hN hρ hρhalf]
  dsimp only [C,N]
  ring

def packetConstant (ρ : ℝ) : ℝ :=
  4+17*(unitFractionalMass ρ)⁻¹*fractionalConstant ρ

theorem packetConstant_pos {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ < 1/2) : 0 < packetConstant ρ := by
  have hM := unitFractionalMass_pos hρ hρhalf
  have hd : 0 < 1-2*ρ := by linarith
  have hf : 0 < fractionalConstant ρ := by unfold fractionalConstant; positivity
  unfold packetConstant
  positivity

/-- Centering a locally Lipschitz row at a point of the parent interval
gives the sharp cell-scale positive Sobolev bound used in the actual
negative-input heat packet. -/
theorem small_amplitude_massive_bound {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (n : ℕ) (x : Grid n) (u : C(AddCircle (1:ℝ),ℂ)) (L : ℝ) (hL : 0 ≤ L)
    (hu : ∀ y ∈ cellSet n x, ‖u y‖ ≤ 2*L/(((2^n:ℕ):ℝ)))
    (hlip : ∀ y ∈ cellSet n x, ∀ w ∈ cellSet n x, ‖u y-u w‖ ≤ L*dist y w) :
    Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff (cut n x u) k‖^2) ∧
      positiveSq Λ ρ (cut n x u) ≤ packetConstant ρ*L^2*(((2^n:ℕ):ℝ))⁻¹^3*
        (Λ+(((2^n:ℕ):ℝ))^2)^ρ := by
  let N : ℝ := ((2^n:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hd : 0 < 1-2*ρ := by linarith
  have hfrac : 0 ≤ fractionalConstant ρ := by unfold fractionalConstant; positivity
  have hM : 0 ≤ (unitFractionalMass ρ)⁻¹ := inv_nonneg.mpr (unitFractionalMass_pos hρ hρhalf).le
  have hg := cut_gagliardo_bound hρ hρhalf n x u (2*L/N) L (by positivity) hL hu hlip
  refine ⟨massive_summable_of_gagliardo hΛ0.le hρ hρhalf _ (cut_memLp n x u) hg.1,?_⟩
  have hb := massive_le_base_gagliardo hΛ0.le hρ hρhalf _ (cut_memLp n x u) hg.1
  have hbase : (∫ y, ‖cut n x u y‖^2 ∂haarAddCircle) ≤ 4*L^2*N⁻¹^3 := by
    exact (cut_square_bound n x u (2*L/N) hu).trans_eq (by dsimp only [N]; field_simp; ring)
  have hG : circleFractionalSq ρ (cut n x u) ≤ 17*fractionalConstant ρ*N^(2*ρ)*L^2*N⁻¹^3 := by
    exact hg.2.trans_eq (by dsimp only [N]; field_simp; ring)
  have hmass : Λ^ρ ≤ (Λ+N^2)^ρ := Real.rpow_le_rpow hΛ0.le (le_add_of_nonneg_right (sq_nonneg _)) hρ.le
  have hmesh : N^(2*ρ) ≤ (Λ+N^2)^ρ := by
    rw [Real.rpow_mul hN.le 2 ρ,Real.rpow_two]
    exact Real.rpow_le_rpow (sq_nonneg _) (le_add_of_nonneg_left hΛ0.le) hρ.le
  have hscaleBase := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hΛ0.le ρ)
  have hscaleG := mul_le_mul_of_nonneg_left hG hM
  have hscaleMass := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 4*L^2*N⁻¹^3)
  have hscaleMesh := mul_le_mul_of_nonneg_right hmesh
    (by positivity : 0 ≤ 17*(unitFractionalMass ρ)⁻¹*fractionalConstant ρ*L^2*N⁻¹^3)
  change positiveSq Λ ρ (cut n x u) ≤ packetConstant ρ*L^2*N⁻¹^3*(Λ+N^2)^ρ
  unfold packetConstant
  nlinarith

end SHE.SmoothCellSobolev
