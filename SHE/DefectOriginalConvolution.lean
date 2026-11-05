module
public import SHE.StrictHistoryOrder
public import SHE.DefectGapDensity
public import SHE.DefectGapKernelMass
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.DefectOriginalConvolution
open Classical
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw OrderedGapCoordinates
open scoped NNReal BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)

def pairKernel (Λ ρ:ℝ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ):ℝ:=
  let z:=separated k ((0:HeatCircle),t,fun _=>0)
  let s:=(carrier L k).terminal z
  ∑i:Fin (1+k),∑j:Fin (1+k),DefectCombinedTime.kernel Λ ρ
    (targets L k z i-s) (targets L k z j-s) (s-q)

def oldFactor (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (k:ℕ)(t:Fin k→ℝ)(A0 ν:ℝ):ℝ:=
  let z:=separated k ((0:HeatCircle),t,fun _=>0)
  timeWeight L ell C k z*DefectRelativeFactor.total L P R.base k z A0 ν

def convolution (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (Λ ρ A0 ν:ℝ)(k:ℕ)(f:ℝ→ℝ):ℝ:=
  ∫t:Fin k→ℝ,
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    if StrictHistory L k z then oldFactor L P ell C k t A0 ν*
      (∫q:ℝ,pairKernel L Λ ρ k t q*f q ∂volume.restrict (Ioc R.base ((carrier L k).terminal z)))
    else 0
    ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))

theorem pair_eq (T:ℝ)(hT:∀x,L.terminal x=T)
    (hroot:∀x i,(L.observations.observations x i).target=T)
    (Λ ρ:ℝ)(k:ℕ)(t:Fin k→ℝ)(q:ℝ)
    (hp:StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0))):
    pairKernel L Λ ρ k t q=DefectGapKernelMass.realKernel Λ ρ k (gaps T k t)
      ((carrier L k).terminal (separated k ((0:HeatCircle),t,fun _=>0))-q):=by
  have ho:=DefectGapOffsets.targets_relative L T hT hroot k t (0:HeatCircle) (fun _=>0) hp
  have hd:∀i,0≤gaps T k t i:=by
    intro i
    have he:=congrFun (PhysicalOrderedGaps.old_gaps_eq L T hT k t (0:HeatCircle) (fun _=>0) hp) i
    rw [←he]
    exact (sub_pos.mpr (CoveredHistoryGeometry.lower_lt_upper L k _ hp i)).le
  unfold pairKernel DefectGapKernelMass.realKernel
  rw [DefectGapKernelMass.offsets_eq k _ hd]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun ho i,congrFun ho j]

/-- Exact q↦terminal−q reflection of the full original current-time
integral, including the original endpoint convention. -/
theorem reflect_integral (a s:ℝ)(has:a≤s)(K f:ℝ→ℝ):
    (∫q:ℝ,K (s-q)*f q ∂volume.restrict (Ioc a s))=
      ∫τ:ℝ,K τ*f (s-τ) ∂volume.restrict (Ioc (0:ℝ) (s-a)):=by
  rw [←intervalIntegral.integral_of_le has,
    show (fun q:ℝ=>K (s-q)*f q)=(fun q:ℝ=>(fun τ=>K τ*f (s-τ)) (s-q)) by
      funext q;congr 2;ring,
    intervalIntegral.integral_comp_sub_left (fun τ=>K τ*f (s-τ)) s,sub_self,
    intervalIntegral.integral_of_le (sub_nonneg.mpr has)]

/-- Literal original-history convolution in exact positive gap/slack
coordinates. This is a change of variables, before any domination or
stochastic square. -/
theorem eq_gap (P:CanonicalCovariance.ProfileParameters)(ell:ℝ)(C:ℕ→ℝ)
    (T:ℝ)(hT:∀x,L.terminal x=T)(hpos:R.base<T)
    (hroot:∀x i,(L.observations.observations x i).target=T)
    (Λ ρ A0 ν:ℝ)(hA0:0≤A0)(hν:0≤ν)(k:ℕ)(f:ℝ→ℝ):
    convolution L P ell C Λ ρ A0 ν k f=
      ∫d:Fin k→ℝ,if (∀i,0<d i) ∧ (∑i,d i)<T-R.base then
        DefectGapDensity.raw P ell C k A0 ν d*
          (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ*f (T-(∑i,d i)-τ)
            ∂volume.restrict (Ioc (0:ℝ) (T-R.base-(∑i,d i))))
      else 0:=by
  have he:convolution L P ell C Λ ρ A0 ν k f=
      ∫t:Fin k→ℝ,if ordered R.base T k t then
        DefectGapDensity.raw P ell C k A0 ν (gaps T k t)*
          (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k (gaps T k t) τ*
            f (T-(∑i,gaps T k t i)-τ)
              ∂volume.restrict (Ioc (0:ℝ) (T-R.base-(∑i,gaps T k t i))))
      else 0 ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon)):=by
    apply integral_congr_ae
    filter_upwards with t
    by_cases hp:StrictHistory L k (separated k ((0:HeatCircle),t,fun _=>0))
    · have hord:ordered R.base T k t:=(StrictHistoryOrder.iff_ordered L T hT hpos k t 0 (fun _=>0)).mp hp
      simp only [convolution,if_pos hp,if_pos hord]
      have hfactor:=DefectGapDensity.actual L P ell C R.base T hT k t (0:HeatCircle) (fun _=>0) hp hA0 hν
      change oldFactor L P ell C k t A0 ν*(∫q:ℝ,pairKernel L Λ ρ k t q*f q
        ∂volume.restrict (Ioc R.base ((carrier L k).terminal (separated k ((0:HeatCircle),t,fun _=>0)))))=_
      rw [show oldFactor L P ell C k t A0 ν=DefectGapDensity.raw P ell C k A0 ν (gaps T k t) from hfactor]
      simp_rw [pair_eq L T hT hroot Λ ρ k t _ hp]
      rw [reflect_integral R.base _ ((carrier L k).terminal_base _)]
      have hs:(carrier L k).terminal (separated k ((0:HeatCircle),t,fun _=>0))=T-∑i,gaps T k t i:=by
        rw [sum_gaps,PhysicalOrderedGaps.terminal_eq_boundary L T hT k t 0 (fun _=>0) hp]
        ring
      rw [hs]
      congr 3
      ring
    · have hord:¬ordered R.base T k t:=fun h=>hp ((StrictHistoryOrder.iff_ordered L T hT hpos k t 0 (fun _=>0)).mpr h)
      simp only [convolution,if_neg hp,if_neg hord]
  rw [he,PhysicalOrderedGaps.ordered_box_integral (le_rfl:R.base≤R.base)
    (by simpa only [hT] using L.terminal_horizon (0:HeatCircle))]
  exact OrderedGapCoordinates.ordered_integral R.base T k
    (fun d=>DefectGapDensity.raw P ell C k A0 ν d*
      (∫τ:ℝ,DefectGapKernelMass.realKernel Λ ρ k d τ*f (T-(∑i,d i)-τ)
        ∂volume.restrict (Ioc (0:ℝ) (T-R.base-(∑i,d i)))))
end SHE.DefectOriginalConvolution
