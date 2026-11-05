module

public import SHE.HaarRealSpace
public import SHE.SignedDamping

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.RealHeat
open MeasureTheory AddCircle CircleHeat FiniteHaar DyadicApproximation
open scoped ENNReal ComplexConjugate
local instance realHeat_circlePositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def conjugate : CircleL2 →L[ℝ] CircleL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 haarAddCircle

theorem conjugate_ae (f : CircleL2) : conjugate f =ᵐ[haarAddCircle] fun x => conj (f x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f

theorem fourierCoeff_conjugate (f : CircleL2) (n : ℤ) :
    fourierCoeff (conjugate f) n=conj (fourierCoeff f (-n)) := by
  unfold fourierCoeff
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [conjugate_ae f] with x hx
  rw [hx]
  simp only [smul_eq_mul,Int.neg_neg,map_mul,← fourier_neg]

theorem conjugate_heat (t : ℝ) (f : CircleL2) : conjugate (heat t f)=heat t (conjugate f) := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr,fourierCoeff_conjugate,heat_fourierCoeff,map_mul]
  congr 1
  simp only [heatWeight,Int.cast_neg,mul_neg,neg_sq,Complex.conj_ofReal]

theorem conjugate_eq_of_real (f : CircleL2) (hf : ∀ᵐ x ∂haarAddCircle,(f x).im=0) :
    conjugate f=f := by
  apply Lp.ext
  filter_upwards [conjugate_ae f,hf] with x hx hr
  rw [hx]
  apply Complex.ext <;> simp [hr]

/-- The literal physical circle heat semigroup preserves the actual
closed real L² subspace, including age zero. -/
theorem heat_real (t : ℝ) (f : CircleL2) (hf : ∀ᵐ x ∂haarAddCircle,(f x).im=0) :
    ∀ᵐ x ∂haarAddCircle,(heat t f x).im=0 := by
  have he : conjugate (heat t f)=heat t f := by
    rw [conjugate_heat,conjugate_eq_of_real f hf]
  have ha := conjugate_ae (heat t f)
  rw [he] at ha
  filter_upwards [ha] with x hx
  have hh := congrArg Complex.im hx
  simp only [Complex.conj_im] at hh
  linarith

def realHeat (t : ℝ) : RealL2 →L[ℝ] RealL2 :=
  (Complex.reCLM.compLpL 2 haarAddCircle).comp ((heat t).restrictScalars ℝ) |>.comp realEmbed

theorem realEmbed_realHeat (t : ℝ) (v : RealL2) :
    realEmbed (realHeat t v)=heat t (realEmbed v) := by
  have hr : ∀ᵐ x ∂haarAddCircle,(realEmbed v x).im=0 := by
    filter_upwards [realEmbed_ae v] with x hx
    rw [hx]
    exact Complex.ofReal_im _
  let w : realCircleSpace := ⟨heat t (realEmbed v),(mem_realCircleSpace _).mpr (heat_real t _ hr)⟩
  exact congrArg Subtype.val (realCircleIdentification.apply_symm_apply w)

theorem realHeat_contraction (t : ℝ) (v : RealL2) : ‖realHeat t v‖ ≤ ‖v‖ := by
  rw [← realEmbed_norm_eq,realEmbed_realHeat]
  exact (heat_contraction t (realEmbed v)).trans_eq (realEmbed_norm_eq v)

theorem realHeat_zero : realHeat 0=ContinuousLinearMap.id ℝ RealL2 := by
  apply ContinuousLinearMap.ext
  intro v
  apply realCircleIdentification.injective
  apply Subtype.ext
  change realEmbed (realHeat 0 v)=realEmbed v
  rw [realEmbed_realHeat,heat_zero,ContinuousLinearMap.id_apply]

theorem realHeat_semigroup {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    realHeat (s+t)=(realHeat s).comp (realHeat t) := by
  apply ContinuousLinearMap.ext
  intro v
  apply realCircleIdentification.injective
  apply Subtype.ext
  change realEmbed (realHeat (s+t) v)=realEmbed (realHeat s (realHeat t v))
  rw [realEmbed_realHeat,realEmbed_realHeat,realEmbed_realHeat,heat_semigroup hs ht]
  rfl

theorem continuous_realHeat_action : Continuous (fun p : ℝ × RealL2 => realHeat p.1 p.2) := by
  have hh := continuous_heat_action.comp
    (continuous_fst.prodMk (realEmbed.continuous.comp continuous_snd))
  exact (Complex.reCLM.compLpL 2 haarAddCircle).continuous.comp hh

end SHE.RealHeat
