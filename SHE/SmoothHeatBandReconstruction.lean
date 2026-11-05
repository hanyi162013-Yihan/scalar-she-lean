module
public import SHE.SmoothScalarField
public import SHE.ScalarHeatBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.SmoothHeatBandReconstruction
open MeasureTheory AddCircle FiniteHaar DyadicApproximation SmoothCylinders
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {a:ℝ→ℝ}(ha:BoundedSmooth a)

def smooth(J:ℕ)(U:RealL2):CircleHeat.CircleL2:=
  SmoothScalarField.value (ScalarHeatBands.smooth_boundedSmooth ha J) U
def band(j:ℕ)(U:RealL2):CircleHeat.CircleL2:=
  SmoothScalarField.value (ScalarHeatBands.band_boundedSmooth ha j) U

theorem band_succ(j:ℕ)(U:RealL2):band ha (j+1) U=smooth ha (j+1) U-smooth ha j U:=
  SmoothScalarField.sub (ScalarHeatBands.smooth_boundedSmooth ha (j+1))
    (ScalarHeatBands.smooth_boundedSmooth ha j) U

/-- A genuine finite high-frequency prefix telescopes at every state.
The lowest block remains separate, including its inhomogeneous band. -/
theorem finite_prefix(J m:ℕ)(U:RealL2):
    (∑r∈Finset.range m,band ha (J+r+1) U)=smooth ha (J+m) U-smooth ha J U:=by
  induction m with
  | zero=>simp only [Finset.range_zero,Finset.sum_empty,Nat.add_zero,sub_self]
  | succ m ih=>
    rw [Finset.sum_range_succ,ih,band_succ]
    have hn:J+(m+1)=J+m+1:=by omega
    rw [hn]
    abel

variable {B K β:ℝ}(hB:∀x,|a x|≤B)(hK:0≤K)(hβ:0≤β)
variable (hh:∀x y,|a x-a y|≤K*|x-y|^β)

include hB hK hβ hh in
/-- The terminal reconstruction error is uniform in the state and in
every smooth approximation having the same original Holder constant. -/
theorem smooth_error(J:ℕ)(U:RealL2):
    ‖smooth ha J U-SmoothScalarField.value ha U‖≤
      K*GaussianAudit.gaussianAbsMoment β*CompactMollifier.radius J^β:=by
  exact SmoothScalarField.error (ScalarHeatBands.smooth_boundedSmooth ha J) ha U
    (mul_nonneg (mul_nonneg hK (GaussianAudit.gaussianAbsMoment_nonneg β))
      (Real.rpow_nonneg (CompactMollifier.radius_pos J).le _)) (ScalarHeatBands.smooth_error ha.smooth.continuous.measurable hB hβ hh J)

variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)
def difference(U V:RealL2):StoppedFourier.CircleL2:=
  OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push (SmoothScalarField.value ha V-SmoothScalarField.value ha U))
def low(J:ℕ)(U V:RealL2):StoppedFourier.CircleL2:=
  OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push (smooth ha J V-smooth ha J U))
def high(j:ℕ)(U V:RealL2):StoppedFourier.CircleL2:=
  OneInputOperator.besselHalf Λ ρ hΛ hρ
    (CircleNormalization.push (band ha (j+1) V-band ha (j+1) U))

theorem high_prefix(J m:ℕ)(U V:RealL2):
    (∑r∈Finset.range m,high ha Λ ρ hΛ hρ (J+r) U V)=
      low ha Λ ρ hΛ hρ (J+m) U V-low ha Λ ρ hΛ hρ J U V:=by
  simp only [high,←map_sum,Finset.sum_sub_distrib,finite_prefix]
  simp only [low,map_sub]
  abel

include hB hK hβ hh in
/-- Quantitative finite-prefix reconstruction in the actual native
massive negative Hilbert norm. The upper-cutoff tail is uniform before
the smoothing index or coupled solution is chosen. -/
theorem reconstruction(J m:ℕ)(U V:RealL2):
    ‖difference ha Λ ρ hΛ hρ U V-low ha Λ ρ hΛ hρ J U V-
      (∑r∈Finset.range m,high ha Λ ρ hΛ hρ (J+r) U V)‖≤
      2*(K*GaussianAudit.gaussianAbsMoment β)*CompactMollifier.radius (J+m)^β:=by
  rw [high_prefix]
  have he:difference ha Λ ρ hΛ hρ U V-low ha Λ ρ hΛ hρ J U V-
      (low ha Λ ρ hΛ hρ (J+m) U V-low ha Λ ρ hΛ hρ J U V)=
      OneInputOperator.besselHalf Λ ρ hΛ hρ (CircleNormalization.push
        ((SmoothScalarField.value ha V-smooth ha (J+m) V)-
          (SmoothScalarField.value ha U-smooth ha (J+m) U))):=by
    simp only [difference,low,map_sub]
    abel
  rw [he]
  calc
    _≤‖CircleNormalization.push ((SmoothScalarField.value ha V-smooth ha (J+m) V)-
        (SmoothScalarField.value ha U-smooth ha (J+m) U))‖:=
      OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _
    _=‖(SmoothScalarField.value ha V-smooth ha (J+m) V)-
        (SmoothScalarField.value ha U-smooth ha (J+m) U)‖:=CircleNormalization.push.norm_map _
    _≤‖SmoothScalarField.value ha V-smooth ha (J+m) V‖+
      ‖SmoothScalarField.value ha U-smooth ha (J+m) U‖:=norm_sub_le _ _
    _≤(K*GaussianAudit.gaussianAbsMoment β*CompactMollifier.radius (J+m)^β)+
      (K*GaussianAudit.gaussianAbsMoment β*CompactMollifier.radius (J+m)^β):=by
        apply add_le_add
        · rw [norm_sub_rev]
          exact smooth_error ha hB hK hβ hh (J+m) V
        · rw [norm_sub_rev]
          exact smooth_error ha hB hK hβ hh (J+m) U
    _=_:=by ring

end SHE.SmoothHeatBandReconstruction
