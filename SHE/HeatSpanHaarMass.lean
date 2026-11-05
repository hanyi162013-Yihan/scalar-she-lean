module

public import SHE.HaarOperator
public import SHE.RealHeatCovarianceMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.HeatProjection
open MeasureTheory Set Real AddCircle HeatTorus HeatTorusKernel FiniteHaar
  GaussianGramScore GaussianIncrement RealHeatCovarianceMean MeasurableGaussianScores
open scoped InnerProductSpace
local instance heatSpanHaarMass_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- A bounded actual factor costs only the dimension of the observed
heat span. The physical centers and every collision remain arbitrary. -/
theorem bounded_haar_projection_mass {q:ℕ}(t:Fin q→ℝ)(a:Fin q→UnitAddCircle)
    (f:CircleHeat.CircleL2)(m U:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤U):
    Summable (fun j:HaarNode=>‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2) ∧
    (∑'j:HaarNode,‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2)≤U*(q:ℝ):=by
  let K:=heatSpan t a
  let b:=stdOrthonormalBasis ℂ K
  let e:Fin (Module.finrank ℂ K)→CircleHeat.CircleL2:=fun i=>(b i:CircleHeat.CircleL2)
  have he:Orthonormal ℂ e:=by
    convert! b.orthonormal.comp_linearIsometry K.subtypeₗᵢ using 1
  have hspan:frameSpan e=K:=by
    have hb:Submodule.span ℂ (Set.range b)=⊤:=by
      simpa only [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
    calc
      _=(Submodule.span ℂ (Set.range b)).map K.subtype:=by
        rw [Submodule.map_span,←Set.range_comp]
        rfl
      _=(⊤:Submodule ℂ K).map K.subtype:=by rw [hb]
      _=K:=by rw [Submodule.map_top,Submodule.range_subtype]
  have hp(j:HaarNode):‖K.starProjection (globalHaarColumn j f)‖^2=
      ∑i:Fin (Module.finrank ℂ K),‖inner ℂ (e i) (globalHaarColumn j f)‖^2:=by
    have hproj:K.starProjection (globalHaarColumn j f)=frameProjection e (globalHaarColumn j f):=by
      simpa only [hspan] using frameProjection_eq_starProjection e he (globalHaarColumn j f)
    rw [hproj,frameProjection_norm_sq _ he]
  have hb(i:Fin (Module.finrank ℂ K)):
      Summable (fun j:HaarNode=>‖inner ℂ (e i) (globalHaarColumn j f)‖^2) ∧
      (∑'j:HaarNode,‖inner ℂ (e i) (globalHaarColumn j f)‖^2)≤U:=by
    have hh:=globalHaarColumn_bessel f m U hm hfreal hf (e i)
    simpa only [norm_inner_symm,he.norm_eq_one i,one_pow,mul_one] using hh
  have hs:Summable (fun j:HaarNode=>∑i:Fin (Module.finrank ℂ K),
      ‖inner ℂ (e i) (globalHaarColumn j f)‖^2):=
    summable_sum (fun i _=>(hb i).1)
  refine ⟨hs.congr (fun j=>(hp j).symm),?_⟩
  change (∑'j:HaarNode,‖K.starProjection (globalHaarColumn j f)‖^2)≤_
  simp_rw [hp]
  rw [Summable.tsum_finsetSum (fun i _=>(hb i).1)]
  calc
    _≤∑_i:Fin (Module.finrank ℂ K),U:=Finset.sum_le_sum (fun i _=>(hb i).2)
    _=U*(Module.finrank ℂ K:ℝ):=by simp;ring
    _≤_:=mul_le_mul_of_nonneg_left (by
      exact_mod_cast (show Module.finrank ℂ K≤q by
        simpa only [K,heatSpan,Set.finrank,Fintype.card_fin] using
          (finrank_range_le_card (R:=ℂ) (fun j:Fin q=>unitHeatKernel (t j) (a j)))))
      (elliptic_upper_nonneg f m U hm hf)

/-- Actual canonical covariance scores of the bounded companion factor
have a finite trace. Only its true Gram domination is used; singular
covariances and colliding observations are allowed. -/
theorem bounded_haar_score_mass {q n:ℕ}{G:Type*}[NormedAddCommGroup G]
    [InnerProductSpace ℝ G][CompleteSpace G]
    (t:Fin q→ℝ)(a:Fin q→UnitAddCircle)(S:State n→ₗ[ℝ]CircleHeat.CircleL2)
    (v:Fin n→G)(hspan:∀z,S z∈heatSpan t a){L:ℝ}(hL:0≤L)
    (hbound:∀z,‖S z‖≤L*‖featureSynthesis v z‖)
    (f:CircleHeat.CircleL2)(m U:ℝ)(hm:0<m)
    (hfreal:∀ᵐy∂haarAddCircle,(f y).im=0)
    (hf:∀ᵐy∂haarAddCircle,m≤(f y).re ∧ (f y).re≤U):
    Summable (fun j:HaarNode=>scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalHaarColumn j f))) ∧
    (∑'j:HaarNode,scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalHaarColumn j f)))≤L^2*U*(q:ℝ):=by
  have hp:=bounded_haar_projection_mass t a f m U hm hfreal hf
  have hscore(j:HaarNode):=scoreVariance_projection_bound t a S v hspan hL hbound (globalHaarColumn j f)
  have hn(j:HaarNode):0≤scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalHaarColumn j f)):=
    scoreVariance_nonneg (Matrix.posSemidef_gram ℝ v) (hscore j).1
  have hs:Summable (fun j:HaarNode=>scoreVariance (Matrix.gram ℝ v) (meanDirection S (globalHaarColumn j f))):=
    Summable.of_nonneg_of_le hn (fun j=>(hscore j).2) (hp.1.mul_left (L^2))
  refine ⟨hs,?_⟩
  calc
    _≤∑'j:HaarNode,L^2*‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2:=
      hs.tsum_le_tsum (fun j=>(hscore j).2) (hp.1.mul_left (L^2))
    _=L^2*(∑'j:HaarNode,‖(heatSpan t a).starProjection (globalHaarColumn j f)‖^2):=tsum_mul_left
    _≤L^2*(U*(q:ℝ)):=mul_le_mul_of_nonneg_left hp.2 (sq_nonneg _)
    _=_:=by ring

end SHE.HeatProjection
