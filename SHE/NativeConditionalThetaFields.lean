module
public import SHE.TwoFreshThetaWordFields
public import SHE.NativeFirstOmittedFields
public import SHE.NativeOmittedCompleteWord
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.NativeConditionalThetaFields
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks
  ControlledOldIntervals OldIntervalCovariance StoppedFourier StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω][MeasurableSpace CircleL2][BorelSpace CircleL2]
variable {n d r m:ℕ}

theorem profile_measurable (P:CanonicalCovariance.ProfileParameters)(Λ:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ):
    Measurable (fun z:Ω×ControlledProfile.Domain=>ControlledProfile.profile P Λ (u z.1) (d0 z.1) (θ z.1,z.2)):=by
  have hm:Measurable (fun z:Ω×ControlledProfile.Domain=>((z.1,θ z.1),z.2)):=
    (measurable_fst.prodMk (hθ.comp measurable_fst)).prodMk measurable_snd
  convert! (ControlledProfile.random_profile_measurable P hu hd Λ).comp hm using 1

theorem residual_measurable (P:CanonicalCovariance.ProfileParameters)(Λ q:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(lo hi:Fin r→ℝ):
    Measurable (fun ω=>ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u ω) (d0 ω) lo hi)) σ target center q (θ ω)):=by
  have hc:=(profile_measurable P Λ u d0 hu hd θ hθ).sub
    ((VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d0 hu hd lo hi).add_const (NativeFirstScoreReserve.floor P))
  convert! StoppedGaussianFields.covariance_measurable
    (VaryingControlledGaussianFields.family (Ω:=Ω) σ target center) hc (measurable_const (a:=q)) using 1

theorem fibre_measurable (P:CanonicalCovariance.ProfileParameters)(Λ q:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(lo hi:Fin r→ℝ)
    (mean:Ω→State n)(hm:Measurable mean)(second:Bool)
    (D:Ω→Fin r→State n)(hD:∀j,Measurable (fun ω=>D ω j))
    (E V:Ω→State n)(hE:Measurable E)(hV:Measurable V)
    (g:Fin d→Fin n)(leaf:Fin m→Fin n)(choices:List (Fin r×Fin (m+1)))
    (F:State d→ℝ)(hF:Measurable F):
    Measurable (fun ω=>TwoFreshFullResidualMoments.fibreAverage P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf choices F):=by
  have hbase(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ ω,(target (leaf j),center (leaf j)))):=by
    have hh:=(profile_measurable P Λ u d0 hu hd θ hθ).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j)))))
    convert! hh using 1
  exact TwoFreshGaussianFields.word_average_measurable _
    (fun j=>VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j)
    D hD _ _ measurable_const (residual_measurable P Λ q u d0 hu hd θ hθ σ target center lo hi)
    E V hE hV second choices P.coefficient P.measurable F hF mean hm g leaf _ hbase

/-- Genuine joint theta/random-reference/current/direction Borel
substitution for the COMPLETE mean or covariance packet. -/
theorem value_measurable (P:CanonicalCovariance.ProfileParameters)(Λ q:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(lo hi:Fin r→ℝ)
    (mean:Ω→State n)(hm:Measurable mean)(second:Bool)
    (D:Ω→Fin r→State n)(hD:∀j,Measurable (fun ω=>D ω j))
    (E V:Ω→State n)(hE:Measurable E)(hV:Measurable V)
    (g:Fin d→Fin n)(leaf:Fin m→Fin n)(F:State d→ℝ)(hF:Measurable F):
    Measurable (fun ω=>TwoFreshCompleteWord.value P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf F):=by
  let cs:=assignments (m:=m+1) (List.finRange r)
  have heq:(fun ω=>TwoFreshCompleteWord.value P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf F)=
      fun ω=>(1/2:ℝ)^r*∑i:Fin cs.length,TwoFreshFullResidualMoments.fibreAverage P Λ (u ω) (d0 ω) (θ ω) q
        σ target center lo hi (mean ω) second (D ω) (E ω) (V ω) g leaf (cs.get i) F:=
    funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact fibre_measurable P Λ q u d0 hu hd θ hθ σ target center lo hi mean hm second D hD E V hE hV g leaf (cs.get i) F hF

theorem omitted_fibre_measurable (P:CanonicalCovariance.ProfileParameters)(Λ q:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(lo hi:Fin r→ℝ)
    (mean:Ω→State n)(hm:Measurable mean)
    (D:Ω→Fin r→State n)(hD:∀j,Measurable (fun ω=>D ω j))
    (E:Ω→State n)(hE:Measurable E)
    (g:Fin d→Fin n)(leaf:Fin m→Fin n)(choices:List (Fin r×Fin (m+1)))(j0:Fin m)
    (F:State d→ℝ)(hF:Measurable F):
    Measurable (fun ω=>NativeFirstOmittedMoments.fibreAverage P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) (D ω) (E ω) g leaf choices j0 F):=by
  have hbase(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ ω,(target (leaf j),center (leaf j)))):=by
    have hh:=(profile_measurable P Λ u d0 hu hd θ hθ).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j)))))
    convert! hh using 1
  exact NativeFirstOmittedFields.word_average_measurable _
    (fun j=>VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j)
    D hD _ _ measurable_const (residual_measurable P Λ q u d0 hu hd θ hθ σ target center lo hi)
    E hE choices j0 P.coefficient P.measurable F hF mean hm g leaf _ hbase

/-- Every omitted leaf retains its original complete assignment sum
under simultaneous theta/random-state substitution. -/
theorem omitted_value_measurable (P:CanonicalCovariance.ProfileParameters)(Λ q:ℝ)
    (u d0:Ω→CircleL2)(hu:Measurable u)(hd:Measurable d0)(θ:Ω→ℝ)(hθ:Measurable θ)
    (σ target:Fin n→ℝ)(center:Fin n→HeatCircle)(lo hi:Fin r→ℝ)
    (mean:Ω→State n)(hm:Measurable mean)
    (D:Ω→Fin r→State n)(hD:∀j,Measurable (fun ω=>D ω j))
    (E:Ω→State n)(hE:Measurable E)
    (g:Fin d→Fin n)(leaf:Fin m→Fin n)(j0:Fin m)(F:State d→ℝ)(hF:Measurable F):
    Measurable (fun ω=>NativeOmittedCompleteWord.value P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) (D ω) (E ω) j0 g leaf F):=by
  let cs:=assignments (m:=m+1) (List.finRange r)
  have heq:(fun ω=>NativeOmittedCompleteWord.value P Λ (u ω) (d0 ω) (θ ω) q
      σ target center lo hi (mean ω) (D ω) (E ω) j0 g leaf F)=
      fun ω=>(1/2:ℝ)^r*∑i:Fin cs.length,if block (cs.get i) j0.succ=[] then
        NativeFirstOmittedMoments.fibreAverage P Λ (u ω) (d0 ω) (θ ω) q
          σ target center lo hi (mean ω) (D ω) (E ω) g leaf (cs.get i) j0 F else 0:=
    funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
  rw [heq]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  by_cases hb:block (cs.get i) j0.succ=[]
  · simp only [hb,ite_true]
    exact omitted_fibre_measurable P Λ q u d0 hu hd θ hθ σ target center lo hi mean hm D hD E hE g leaf (cs.get i) j0 F hF
  · simp only [hb,ite_false]
    exact measurable_const
end SHE.NativeConditionalThetaFields
