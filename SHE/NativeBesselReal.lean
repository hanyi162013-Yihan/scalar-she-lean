module

public import SHE.NativeHeatObservation
public import SHE.OneInputOperator

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.NativeBesselReal
open MeasureTheory AddCircle Real StoppedFourier DyadicApproximation
open scoped ENNReal ComplexConjugate
local instance nativeBesselReal_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeBesselReal_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

def conjugate : CircleL2 →L[ℝ] CircleL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 haarAddCircle

theorem conjugate_ae (v : CircleL2) :
    conjugate v=ᵐ[haarAddCircle] fun x => conj (v x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL v

theorem fourierCoeff_conjugate (v : CircleL2) (i : ℤ) :
    fourierCoeff (conjugate v) i=conj (fourierCoeff v (-i)) := by
  unfold fourierCoeff
  rw [←integral_conj]
  apply integral_congr_ae
  filter_upwards [conjugate_ae v] with x hx
  rw [hx]
  simp only [smul_eq_mul,Int.neg_neg,map_mul,←fourier_neg]

theorem conjugate_bessel (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : CircleL2) :
    conjugate (OneInputOperator.besselHalf Λ ρ hΛ hρ v)=
      OneInputOperator.besselHalf Λ ρ hΛ hρ (conjugate v) := by
  apply (fourierBasis (T:=2*Real.pi)).repr.injective
  apply lp.ext
  funext i
  simp only [fourierBasis_repr,fourierCoeff_conjugate,OneInputOperator.besselHalf_fourierCoeff,
    map_mul,Int.cast_neg,neg_sq,Complex.conj_ofReal]

theorem conjugate_eq_of_real (v : CircleL2)
    (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) : conjugate v=v := by
  apply Lp.ext
  filter_upwards [conjugate_ae v,hv] with x hx hr
  rw [hx]
  apply Complex.ext <;> simp [hr]

/-- The native massive Bessel multiplier preserves the actual real
subspace. Its symbol is the native (Λ+k²)^(-ρ/2), not the unit-circle
heat generator with an omitted 4π² scale. -/
theorem bessel_real (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : CircleL2)
    (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) :
    ∀ᵐ x ∂haarAddCircle,(OneInputOperator.besselHalf Λ ρ hΛ hρ v x).im=0 := by
  have he : conjugate (OneInputOperator.besselHalf Λ ρ hΛ hρ v)=
      OneInputOperator.besselHalf Λ ρ hΛ hρ v := by
    rw [conjugate_bessel,conjugate_eq_of_real v hv]
  have ha := conjugate_ae (OneInputOperator.besselHalf Λ ρ hΛ hρ v)
  rw [he] at ha
  filter_upwards [ha] with x hx
  have hh := congrArg Complex.im hx
  simp only [Complex.conj_im] at hh
  linarith

/-- Return a native real field to the original real unit-circle state
space used by the supplied Itô integral. -/
def part : CircleL2 →L[ℝ] RealL2 :=
  (Complex.reCLM.compLpL 2 (haarAddCircle (T:=1))).comp
    (CircleNormalization.push.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

theorem embed_part (v : CircleL2) (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) :
    NativeHeatObservation.embed (part v)=v := by
  change CircleNormalization.push (realEmbed (realPart (CircleNormalization.push.symm v)))=v
  have hu : ∀ᵐ x ∂(haarAddCircle (T:=1)),(CircleNormalization.push.symm v x).im=0 :=
    CircleNormalization.push_symm_ae_property v (fun z : ℂ => z.im=0) hv
  have he : realEmbed (realPart (CircleNormalization.push.symm v))=CircleNormalization.push.symm v :=
    NativeHeatObservation.realEmbed_realPart_of_real _ hu
  exact (congrArg CircleNormalization.push he).trans (CircleNormalization.push.apply_symm_apply v)

theorem part_embed (v : RealL2) : part (NativeHeatObservation.embed v)=v := by
  change realPart (CircleNormalization.push.symm (CircleNormalization.push (realEmbed v)))=v
  rw [CircleNormalization.push.symm_apply_apply]
  exact FiniteHaar.realCircleIdentification.left_inv v

theorem part_norm (v : CircleL2) (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) :
    ‖part v‖=‖v‖ := by
  rw [←NativeHeatObservation.embed_norm,embed_part v hv]

def bessel (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) : RealL2 →L[ℝ] RealL2 :=
  part.comp (((OneInputOperator.besselHalf Λ ρ hΛ hρ).restrictScalars ℝ).comp NativeHeatObservation.embed)

theorem embed_bessel (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (v : RealL2) :
    NativeHeatObservation.embed (bessel Λ ρ hΛ hρ v)=
      OneInputOperator.besselHalf Λ ρ hΛ hρ (NativeHeatObservation.embed v) := by
  have hu : ∀ᵐ x ∂(haarAddCircle (T:=1)),(realEmbed v x).im=0 :=
    (realEmbed_ae v).mono (fun x hx => by rw [hx];exact Complex.ofReal_im _)
  have hn : ∀ᵐ x ∂(haarAddCircle (T:=2*Real.pi)),(NativeHeatObservation.embed v x).im=0 :=
    CircleNormalization.push_ae_property (realEmbed v) (fun z : ℂ => z.im=0) hu
  exact embed_part _ (bessel_real Λ ρ hΛ hρ _ hn)

theorem bessel_heat (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) {t : ℝ} (ht : 0 ≤ t)
    (v : RealL2) :
    NativeHeatObservation.embed (bessel Λ ρ hΛ hρ (NativeHeatObservation.heat t v))=
      OneInputOperator.besselHalf Λ ρ hΛ hρ
        (circleHeatOperator t ht (NativeHeatObservation.embed v)) := by
  rw [embed_bessel,NativeHeatObservation.embed_heat ht]

end SHE.NativeBesselReal
