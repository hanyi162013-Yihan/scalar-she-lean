module
public import SHE.DefectOriginalEnvelope
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
namespace SHE.DefectOriginalEnvelopeIntegral
open Set MeasureTheory Real AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry HistoryProductMeasure OrderedGapCoordinates
open scoped BigOperators
open Classical
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

/-- The joint positive norm envelope integrates to the literal original
convolution, with all original endpoint pairs and time restrictions. -/
theorem integral_eq (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (hroot:∀x i,(L.observations.observations x i).target=T)
    (Λ ρ A0 ν:ℝ)(k:ℕ)(f:ℝ→ℝ)
    (hi:Integrable (DefectOriginalEnvelope.value L P ell C T Λ ρ A0 ν k f)
      ((Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))).prod volume)):
    (∫p:(Fin k→ℝ)×ℝ,DefectOriginalEnvelope.value L P ell C T Λ ρ A0 ν k f p
      ∂(Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))).prod volume)=
        DefectOriginalConvolution.convolution L P ell C Λ ρ A0 ν k f:=by
  rw [integral_prod _ hi]
  unfold DefectOriginalConvolution.convolution
  apply integral_congr_ae
  filter_upwards with t
  dsimp only
  by_cases hp:StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0))
  · rw [if_pos hp]
    have hW:DefectOldTimeMass.weight L P ell C k A0 ν t=
        DefectOriginalConvolution.oldFactor L P ell C k t A0 ν:=by
      simp only [DefectOldTimeMass.weight,if_pos hp]
    have hs:DefectOriginalEnvelope.edge T k t=
        (carrier L k).terminal (separated k ((0:HeatCircle),t,fun _=>0)):=by
      rw [DefectOriginalEnvelope.edge,sum_gaps,
        PhysicalOrderedGaps.terminal_eq_boundary L T hT k t 0 (fun _=>0) hp]
      ring
    have hI:(fun q:ℝ=>DefectOriginalEnvelope.value L P ell C T Λ ρ A0 ν k f (t,q))=
        fun q:ℝ=>DefectOldTimeMass.weight L P ell C k A0 ν t*
          (Ioc R.base (DefectOriginalEnvelope.edge T k t)).indicator
            (fun q=>DefectGapKernelMass.realKernel Λ ρ k (gaps T k t)
              (DefectOriginalEnvelope.edge T k t-q)*f q) q:=by
      funext q
      by_cases hq:R.base<q ∧ q≤DefectOriginalEnvelope.edge T k t
      · simp only [DefectOriginalEnvelope.value,Set.indicator,Set.mem_Ioc,if_pos hq]
      · simp only [DefectOriginalEnvelope.value,Set.indicator,Set.mem_Ioc,if_neg hq]
    rw [hI,integral_const_mul,integral_indicator measurableSet_Ioc,hW,hs]
    congr 1
    apply integral_congr_ae
    filter_upwards with q
    rw [DefectOriginalConvolution.pair_eq L T hT hroot Λ ρ k t q hp]
  · rw [if_neg hp]
    have he(q:ℝ):DefectOriginalEnvelope.value L P ell C T Λ ρ A0 ν k f (t,q)=0:=by
      change (if StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0)) then _ else 0)*_=0
      rw [if_neg hp,zero_mul]
    simp only [he,integral_zero]
end SHE.DefectOriginalEnvelopeIntegral
