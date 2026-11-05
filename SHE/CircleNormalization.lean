module

public import SHE.HaarDamping
public import SHE.HistoryFrames
public import SHE.OneInputOperator
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.CircleNormalization
open MeasureTheory AddCircle
open scoped ENNReal

variable (P Q : ℝ) [hP : Fact (0 < P)] [hQ : Fact (0 < Q)]

/-- The physical rescaling between two circle periods. -/
def scale : AddCircle P ≃+ AddCircle Q :=
  AddCircle.equivAddCircle P Q hP.out.ne' hQ.out.ne'

theorem continuous_scale : Continuous (scale P Q) :=
  AddCircle.continuous_equivAddCircle P Q hP.out.ne' hQ.out.ne'

def scaleMeasurableEquiv : AddCircle P ≃ᵐ AddCircle Q :=
  (AddCircle.homeomorphAddCircle P Q hP.out.ne' hQ.out.ne').toMeasurableEquiv

/-- Normalized Haar measure is exactly preserved; no volume constant is
discarded when changing the circle convention. -/
theorem scale_measurePreserving :
    MeasurePreserving (scale P Q) (haarAddCircle (T:=P)) (haarAddCircle (T:=Q)) := by
  exact (scale P Q).toAddMonoidHom.measurePreserving (continuous_scale P Q)
    (scale P Q).surjective (by simp)

def pull : Lp ℂ 2 (haarAddCircle (T:=Q)) →ₗᵢ[ℂ] Lp ℂ 2 (haarAddCircle (T:=P)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (scale P Q) (scale_measurePreserving P Q)

theorem pull_ae (f : Lp ℂ 2 (haarAddCircle (T:=Q))) :
    pull P Q f =ᵐ[haarAddCircle (T:=P)] fun x => f (scale P Q x) :=
  Lp.coeFn_compMeasurePreserving f (scale_measurePreserving P Q)

theorem pull_ae_property (f : Lp ℂ 2 (haarAddCircle (T:=Q))) (p : ℂ → Prop)
    (hf : ∀ᵐ x ∂haarAddCircle (T:=Q), p (f x)) :
    ∀ᵐ x ∂haarAddCircle (T:=P), p (pull P Q f x) := by
  filter_upwards [pull_ae P Q f, (scale_measurePreserving P Q).quasiMeasurePreserving.ae hf]
    with x hx hp
  rw [hx]
  exact hp

theorem fourier_scale (n : ℤ) (x : AddCircle P) :
    fourier (T:=Q) n (scale P Q x) = fourier (T:=P) n x := by
  induction x using Quotient.inductionOn with
  | _ r =>
    rw [scale,AddCircle.equivAddCircle_apply_mk,fourier_coe_apply,fourier_coe_apply]
    congr 1
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hP.out.ne', Complex.ofReal_ne_zero.mpr hQ.out.ne']

theorem fourierCoeff_pull (f : Lp ℂ 2 (haarAddCircle (T:=Q))) (n : ℤ) :
    fourierCoeff (pull P Q f) n = fourierCoeff f n := by
  unfold fourierCoeff
  calc
    _ = ∫ x : AddCircle P, fourier (-n) x • f (scale P Q x) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [pull_ae P Q f] with x hx
      rw [hx]
    _ = ∫ x : AddCircle P, fourier (T:=Q) (-n) (scale P Q x) • f (scale P Q x)
        ∂haarAddCircle := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change fourier (T:=P) (-n) x • f (scale P Q x) =
          fourier (T:=Q) (-n) (scale P Q x) • f (scale P Q x)
        rw [fourier_scale])
    _ = _ := (scale_measurePreserving P Q).integral_comp
      (scaleMeasurableEquiv P Q).measurableEmbedding
      (fun x : AddCircle Q => fourier (-n) x • f x)

theorem pull_inverse (f : Lp ℂ 2 (haarAddCircle (T:=P))) :
    pull P Q (pull Q P f) = f := by
  apply (fourierBasis (T:=P)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr,fourierCoeff_pull]

/-- The literal physical rescaling is a complex linear isometry
equivalence between the two normalized circle `L²` spaces. -/
def equivalence : Lp ℂ 2 (haarAddCircle (T:=Q)) ≃ₗᵢ[ℂ] Lp ℂ 2 (haarAddCircle (T:=P)) :=
  LinearIsometryEquiv.ofSurjective (pull P Q) (fun f => ⟨pull Q P f,pull_inverse P Q f⟩)

theorem equivalence_symm_apply (f : Lp ℂ 2 (haarAddCircle (T:=P))) :
    (equivalence P Q).symm f = pull Q P f := by
  apply (equivalence P Q).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (pull_inverse P Q f).symm

local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Unit-period physical fields in the manuscript's other Fourier
normalization, with period `2π`. -/
def push : CircleHeat.CircleL2 ≃ₗᵢ[ℂ] StoppedFourier.CircleL2 :=
  equivalence (2*Real.pi) 1

theorem push_ae (f : CircleHeat.CircleL2) :
    push f =ᵐ[haarAddCircle (T:=2*Real.pi)] fun x => f (scale (2*Real.pi) 1 x) :=
  pull_ae _ _ f

theorem fourierCoeff_push (f : CircleHeat.CircleL2) (n : ℤ) :
    fourierCoeff (push f) n = fourierCoeff f n := fourierCoeff_pull _ _ f n

theorem push_ae_property (f : CircleHeat.CircleL2) (p : ℂ → Prop)
    (hf : ∀ᵐ x ∂haarAddCircle (T:=1), p (f x)) :
    ∀ᵐ x ∂haarAddCircle (T:=2*Real.pi), p (push f x) := pull_ae_property _ _ f p hf

theorem push_symm_ae_property (f : StoppedFourier.CircleL2) (p : ℂ → Prop)
    (hf : ∀ᵐ x ∂haarAddCircle (T:=2*Real.pi), p (f x)) :
    ∀ᵐ x ∂haarAddCircle (T:=1), p (push.symm f x) := by
  change ∀ᵐ x ∂haarAddCircle (T:=1), p ((equivalence (2*Real.pi) 1).symm f x)
  rw [equivalence_symm_apply]
  exact pull_ae_property _ _ f p hf

/-- The generator changes by `(2π)²`. This identity connects the actual
two circle semigroups without hiding the time normalization constant. -/
theorem push_heat (t : ℝ) (ht : 0 ≤ t) (f : CircleHeat.CircleL2) :
    push (CircleHeat.heat t f) = StoppedFourier.circleHeatOperator ((2*Real.pi)^2*t)
      (mul_nonneg (sq_nonneg _) ht) (push f) := by
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr,fourierCoeff_push,CircleHeat.heat_fourierCoeff,
    StoppedFourier.circleHeatOperator_fourierCoeff,CircleHeat.heatWeight,max_eq_left ht]
  rw [show -t * (2*Real.pi*(n:ℝ))^2 = -((2*Real.pi)^2*t)*(n:ℝ)^2 by ring]

/-- The massive negative coefficient input in the Haar estimate is
exactly the actual Bessel half-operator energy after physical rescaling. -/
theorem push_bessel_energy {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (f : CircleHeat.CircleL2) :
    ‖OneInputOperator.besselHalf Λ ρ hΛ hρ (push f)‖ ^ 2 =
      StepInput.negativeEnergy 1 Λ ρ f := by
  rw [OneInputOperator.norm_sq_fourier]
  unfold StepInput.negativeEnergy CircleHeat.weightedFourierSq
  apply tsum_congr
  intro n
  rw [OneInputOperator.besselHalf_fourierCoeff,fourierCoeff_push,norm_mul,mul_pow]
  rw [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  unfold CircleHeat.massiveWeight
  dsimp only
  rw [one_mul,← Real.rpow_mul_natCast (by positivity : (0:ℝ) ≤ Λ+(n:ℝ)^2),
    ← Real.rpow_neg (by positivity : (0:ℝ) ≤ Λ+(n:ℝ)^2)]
  congr 2
  ring

end SHE.CircleNormalization
