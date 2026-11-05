module

public import SHE.FourierCluster
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.FourierHeatLine
open MeasureTheory SHE.HeatLine SHE.FourierCluster
open scoped FourierTransform

def heatMass (t : ℝ) : ℝ := Real.sqrt (4*Real.pi*t)

theorem heatMass_pos {t : ℝ} (ht : 0 < t) : 0 < heatMass t := by unfold heatMass; positivity

/-- The exact real-line heat transform in the standard Fourier convention,
including the physical normalization needed by Poisson summation. -/
theorem fourier_heatEntire {t : ℝ} (ht : 0 < t) (a ξ : ℝ) :
    𝓕 (fun x : ℝ => heatEntire t a (x:ℂ)) ξ =
      (heatMass t:ℂ)*frequencyGaussian t a (ξ:ℂ) := by
  let b : ℂ := ((-1/(4*t):ℝ):ℂ)
  let c : ℂ := ((a/(2*t):ℝ):ℂ)-((2*Real.pi*ξ:ℝ):ℂ)*Complex.I
  let d : ℂ := ((-a^2/(4*t):ℝ):ℂ)
  have hb : b.re < 0 := by dsimp only [b,Complex.ofReal_re]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hint (x : ℝ) : ((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I-
      ((x:ℂ)-(a:ℂ))^2/(4*(t:ℂ)) = b*(x:ℂ)^2+c*(x:ℂ)+d := by
    dsimp only [b,c,d]
    push_cast
    field_simp
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul,heatEntire,← Complex.exp_add]
  simp_rw [show ∀ x : ℝ,(((-2*Real.pi*x*ξ:ℝ):ℂ)*Complex.I)+
      -(((x:ℂ)-(a:ℂ))^2)/(4*(t:ℂ)) = b*(x:ℂ)^2+c*(x:ℂ)+d from
        fun x => by simpa only [sub_eq_add_neg,neg_div] using hint x]
  rw [integral_cexp_quadratic hb c d]
  have hbase : (Real.pi:ℂ)/(-b) = ((4*Real.pi*t:ℝ):ℂ) := by
    dsimp only [b]
    push_cast
    field_simp
  have hmass : ((Real.pi:ℂ)/(-b))^(1/2:ℂ) = (heatMass t:ℂ) := by
    rw [hbase]
    have hnonneg : 0 ≤ 4*Real.pi*t := by positivity
    rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,← Complex.ofReal_cpow hnonneg (1/2:ℝ)]
    congr 1
    exact (Real.sqrt_eq_rpow _).symm
  rw [hmass]
  congr 1
  unfold frequencyGaussian SHE.HeatAnnihilator.gaussian frequencyParameter
  congr 1
  dsimp only [b,c,d]
  push_cast
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

end SHE.FourierHeatLine
