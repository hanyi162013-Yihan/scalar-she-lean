module

public import SHE.RealInnovationIdentity
public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FiniteHaar
open MeasureTheory AddCircle CircleHeat DyadicApproximation
open scoped ENNReal
local instance haarPhysicalAnalysis_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance haarPhysicalAnalysis_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

theorem rootEquivalence_self_adjoint {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) :
    (CircleMultiplier.rootEquivalence f.1 ell M hell
      (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2))).toContinuousLinearMap.adjoint=
    (CircleMultiplier.rootEquivalence f.1 ell M hell
      (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2))).toContinuousLinearMap := by
  change (CircleMultiplier.operator (CircleMultiplier.rootCoefficient f.1 M (f.2.2.mono (fun _ h => h.2)))
    (Real.sqrt M) (CircleMultiplier.rootCoefficient_norm_bound f.1 M (f.2.2.mono (fun _ h => h.2)))).adjoint=
    CircleMultiplier.operator (CircleMultiplier.rootCoefficient f.1 M (f.2.2.mono (fun _ h => h.2)))
      (Real.sqrt M) (CircleMultiplier.rootCoefficient_norm_bound f.1 M (f.2.2.mono (fun _ h => h.2)))
  exact CircleMultiplier.operator_adjoint _ _ _ (CircleMultiplier.rootCoefficient_real f.1 M _)

/-- The literal common-Haar analysis row is the actual innovation
rotation of the physical square-root multiplier. -/
theorem factorAnalysis_innovation {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) (v : CircleL2) :
    factorAnalysis f.1 ell M hell f.2.1 f.2.2 v=
      innovationRotation f.1 ell M hell f.2.1 f.2.2
        (CircleMultiplier.rootEquivalence f.1 ell M hell
          (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) v) := by
  let J := innovationRotation f.1 ell M hell f.2.1 f.2.2
  let R := (CircleMultiplier.rootEquivalence f.1 ell M hell
    (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2))).toContinuousLinearMap
  have he : (fieldFactor ell M hell f).comp (J : CircleL2 →L[ℂ] HaarInput)=R := by
    apply ContinuousLinearMap.ext
    intro x
    exact factor_innovationRotation f.1 ell M hell f.2.1 f.2.2 x
  have ha := congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => T.adjoint) he
  rw [ContinuousLinearMap.adjoint_comp,LinearIsometryEquiv.adjoint_eq_symm] at ha
  have hR : R.adjoint=R := rootEquivalence_self_adjoint hell f
  change (J.symm : HaarInput →L[ℂ] CircleL2).comp
    (factorAnalysis f.1 ell M hell f.2.1 f.2.2).adjoint.adjoint=R.adjoint at ha
  rw [ContinuousLinearMap.adjoint_adjoint,hR] at ha
  have hx := congrArg (fun T : CircleL2 →L[ℂ] CircleL2 => J (T v)) ha
  change J (J.symm (factorAnalysis f.1 ell M hell f.2.1 f.2.2 v))=J (R v) at hx
  rw [LinearIsometryEquiv.apply_symm_apply] at hx
  exact hx

theorem realInputPart_embed (v : RealHaarInput) : realInputPart (realInputEmbed v)=v := by
  apply lp.ext
  funext q
  exact Complex.ofReal_re _

/-- Exact physical input represented by every real Haar analysis row. -/
theorem realFactorAnalysis_innovation {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M) (v : RealL2) :
    realInputPart (factorAnalysis f.1 ell M hell f.2.1 f.2.2 (realEmbed v))=
      fieldRealInnovation ell M hell f
        (realPart (CircleMultiplier.rootEquivalence f.1 ell M hell
          (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v))) := by
  let z := CircleMultiplier.rootEquivalence f.1 ell M hell
    (f.2.2.mono (fun _ h => h.1)) (f.2.2.mono (fun _ h => h.2)) (realEmbed v)
  have hz : ∀ᵐ x ∂haarAddCircle,(z x).im=0 := by
    exact CircleMultiplier.operator_real_ae _ (Real.sqrt M)
      (CircleMultiplier.rootCoefficient_norm_bound f.1 M _) (CircleMultiplier.rootCoefficient_real f.1 M _)
      (realEmbed v) ((mem_realCircleSpace _).mp (realCircleIdentification v).2)
  have he := realInnovation_embed hell f (realPart z)
  rw [NativeHeatObservation.realEmbed_realPart_of_real z hz] at he
  have ha := factorAnalysis_innovation hell f (realEmbed v)
  change factorAnalysis f.1 ell M hell f.2.1 f.2.2 (realEmbed v)=
    innovationRotation f.1 ell M hell f.2.1 f.2.2 z at ha
  rw [← he] at ha
  have hh := congrArg realInputPart ha
  rw [realInputPart_embed] at hh
  exact hh

end SHE.FiniteHaar
