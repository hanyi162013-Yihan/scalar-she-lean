module

public import SHE.OneInputOperator
public import SHE.PhysicalProfile

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace SHE.NativeFourierAverage
open MeasureTheory AddCircle StoppedFourier
open scoped ENNReal
local instance nativeFourierAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- A Fourier coordinate as a genuine continuous linear functional. -/
def coefficient (n : ℤ) : CircleL2 →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ=>ℂ) 2 n).comp
    (fourierBasis (T:=2*Real.pi)).repr.toLinearIsometry.toContinuousLinearMap

theorem coefficient_apply (n : ℤ) (v : CircleL2) : coefficient n v=fourierCoeff v n := by
  change (fourierBasis (T:=2*Real.pi)).repr v n=fourierCoeff v n
  exact fourierBasis_repr v n

theorem coefficient_integral {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (v : A→CircleL2) (hv : Integrable v ν) (n : ℤ) :
    fourierCoeff (∫ a,v a ∂ν : CircleL2) n=∫ a,fourierCoeff (v a) n ∂ν := by
  simpa only [coefficient_apply] using ((coefficient n).integral_comp_comm hv).symm

/-- Fourier coefficients commute with a scalar parameter integral under
the actual product L¹ hypothesis, without any L² hypothesis on its average. -/
theorem scalar_coefficient_integral {A : Type*} [MeasurableSpace A] (ν : Measure A)
    [SFinite ν] (g : A×HeatCircle→ℂ) (hg : Integrable g (ν.prod haarAddCircle)) (n : ℤ) :
    fourierCoeff (fun x=>∫ a,g (a,x) ∂ν) n=
      ∫ a,fourierCoeff (fun x=>g (a,x)) n ∂ν := by
  have hi : Integrable (fun z : A×HeatCircle=>fourier (-n) z.2*g z) (ν.prod haarAddCircle) := by
    exact hg.bdd_mul (((fourier (-n)).continuous.measurable.comp measurable_snd).aestronglyMeasurable)
      (ae_of_all _ (fun z=>show ‖fourier (-n) z.2‖≤(1:ℝ) by simp [fourier_apply]))
  simp only [fourierCoeff,smul_eq_mul]
  simp_rw [←integral_const_mul]
  exact (integral_integral_swap hi).symm

/-- Weighted Fourier identification survives a genuine Bochner/scalar
parameter average. In particular the scalar average need only be L¹. -/
theorem weighted_average {A : Type*} [MeasurableSpace A] (ν : Measure A) [SFinite ν]
    (v : A→CircleL2) (g : A×HeatCircle→ℂ) (hv : Integrable v ν)
    (hg : Integrable g (ν.prod haarAddCircle)) (w : ℤ→ℂ)
    (h : ∀ᵐ a ∂ν,∀ n,fourierCoeff (v a) n=w n*fourierCoeff (fun x=>g (a,x)) n) :
    ∀ n,fourierCoeff (∫ a,v a ∂ν : CircleL2) n=
      w n*fourierCoeff (fun x=>∫ a,g (a,x) ∂ν) n := by
  intro n
  rw [coefficient_integral ν v hv,scalar_coefficient_integral ν g hg]
  calc
    (∫ a,fourierCoeff (v a) n ∂ν)=∫ a,w n*fourierCoeff (fun x=>g (a,x)) n ∂ν :=
      integral_congr_ae (h.mono (fun a ha=>ha n))
    _=w n*(∫ a,fourierCoeff (fun x=>g (a,x)) n ∂ν) := integral_const_mul _ _

end SHE.NativeFourierAverage
