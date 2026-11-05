module
public import SHE.NativeTwoPointHeatGram
public import SHE.StoppedCovarianceSplit
public import SHE.StoppedCovarianceOrder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeTwoPointCovariance
open Real Set MeasureTheory StoppedFourier StoppedGaussianFeatures GaussianGramScore
open scoped BigOperators InnerProductSpace Matrix
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩

/-- Dimension-only native physical small-time cutoff. -/
def horizon:ℝ:=min 1 (Classical.choose NativeTwoPointHeatGram.separated_lower)
theorem horizon_pos:0<horizon:=lt_min zero_lt_one (Classical.choose_spec NativeTwoPointHeatGram.separated_lower).1

def centers(x y:HeatCircle):Fin 2→HeatCircle:=![x,y]
def matrix(h κ:ℝ)(x y:HeatCircle):Matrix (Fin 2) (Fin 2) ℝ:=
  stoppedCovariance (fun _=>h) (fun _=>h) (centers x y) (fun _=>κ) 0

def history(h:ℝ)(x y:HeatCircle)(z:Fin 2→ℝ)(s:ℝ):CircleL2:=
  historyF Finset.univ (fun i=>(z i:ℂ)) (fun _=>h) (fun _=>h) (centers x y) s

theorem history_integrable(h:ℝ)(x y:HeatCircle)(z:Fin 2→ℝ):
    IntegrableOn (fun s=>‖history h x y z s‖^2) (Ici (0:ℝ)):=by
  have hm:=historyF_memLp_time Finset.univ (fun i=>(z i:ℂ)) (fun _=>h) (fun _=>h)
    (centers x y) (fun _ _=>le_rfl) 0
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

theorem history_before{h s:ℝ}(hs:s<h)(x y:HeatCircle)(z:Fin 2→ℝ):
    history h x y z s=(z 0:ℂ)•circleHeat (h-s) x+(z 1:ℂ)•circleHeat (h-s) y:=by
  simp only [history,historyF,Fin.sum_univ_two,if_pos hs,centers,Matrix.cons_val_zero,Matrix.cons_val_one]

/-- The true integrated native two-point heat history has the expected
linear-distance/square-root-time lower bound, including coincident points. -/
theorem history_lower{h:ℝ}(hh:0<h)(hhH:h≤horizon)(x y:HeatCircle)(z:Fin 2→ℝ):
    (min (dist x y) (sqrt h)/128)*(z 0^2+z 1^2)≤
      ∫s in Ici (0:ℝ),‖history h x y z s‖^2:=by
  let W:=z 0^2+z 1^2
  have hW:0≤W:=add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hi:=history_integrable h x y z
  by_cases hd:dist x y=0
  · simp only [hd,min_eq_left (sqrt_nonneg _),zero_div,zero_mul]
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hd0:0<dist x y:=lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  let r:=min h ((dist x y)^2/16)
  have hr:0<r:=lt_min hh (div_pos (sq_pos_of_pos hd0) (by norm_num))
  have hrh:r≤h:=min_le_left _ _
  have hrd:r≤(dist x y)^2/16:=min_le_right _ _
  have hsep:4*sqrt r≤dist x y:=by
    apply (sq_le_sq₀ (by positivity) dist_nonneg).mp
    rw [mul_pow,sq_sqrt hr.le]
    norm_num
    linarith
  let J:=Ioc (h-r) (h-r/2)
  have hsub:J⊆Ici (0:ℝ):=by intro s hs;exact le_of_lt (lt_of_le_of_lt (by linarith) hs.1)
  have hJ:IntegrableOn (fun s=>‖history h x y z s‖^2) J:=hi.mono_set hsub
  let C:=W/(16*sqrt r)
  have hc:Integrable (fun _:ℝ=>C) (volume.restrict J):=integrable_const _
  have hsec:∀s∈J,C≤‖history h x y z s‖^2:=by
    intro s hs
    rcases hs with ⟨hslo,hshi⟩
    have hs0:0<h-s:=by linarith
    have hsR:h-s≤r:=by linarith
    have hsH:h-s≤Classical.choose NativeTwoPointHeatGram.separated_lower:=
      hsR.trans (hrh.trans (hhH.trans (min_le_right _ _)))
    have hssep:4*sqrt (h-s)≤dist x y:=
      (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hsR) (by norm_num)).trans hsep
    have hb:=(Classical.choose_spec NativeTwoPointHeatGram.separated_lower).2
      (h-s) hs0 hsH x y hssep (z 0) (z 1)
    rw [history_before (sub_pos.mp hs0)]
    apply le_trans _ hb
    exact div_le_div_of_nonneg_left hW (by positivity) (mul_le_mul_of_nonneg_left (sqrt_le_sqrt hsR) (by norm_num))
  have hlow:(∫s in J,C)≤∫s in J,‖history h x y z s‖^2:=by
    apply integral_mono_ae hc hJ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hsec s hs
  have hmono:(∫s in J,‖history h x y z s‖^2)≤∫s in Ici (0:ℝ),‖history h x y z s‖^2:=
    setIntegral_mono_set hi (ae_of_all _ (fun _=>sq_nonneg _)) (ae_of_all _ hsub)
  have hconst:(∫s in J,C)=W*sqrt r/32:=by
    rw [integral_const,Measure.real,Measure.restrict_apply_univ]
    change (volume.real J)*C=_
    rw [Real.volume_real_Ioc_of_le (by linarith: h-r≤h-r/2)]
    dsimp only [C]
    have hsq:=sq_sqrt hr.le
    field_simp
    nlinarith
  have hmass:W*sqrt r/32≤∫s in Ici (0:ℝ),‖history h x y z s‖^2:=hconst.symm.trans_le (hlow.trans hmono)
  let m:=min (dist x y) (sqrt h)
  have hm0:0≤m:=le_min dist_nonneg (sqrt_nonneg _)
  have hmd:m≤dist x y:=min_le_left _ _
  have hmh:m≤sqrt h:=min_le_right _ _
  have hmr:m/4≤sqrt r:=by
    apply le_sqrt_of_sq_le
    apply le_min
    · have he:=pow_le_pow_left₀ hm0 hmh 2
      rw [sq_sqrt hh.le] at he
      nlinarith [sq_nonneg m]
    · have he:=pow_le_pow_left₀ hm0 hmd 2
      nlinarith
  have he:=mul_le_mul_of_nonneg_left hmr hW
  dsimp only [W,m] at he hmass ⊢
  linarith

/-- The matrix is the literal native stopped covariance with BOTH
stops and targets equal to h, and constant common additive density κ. -/
theorem lower{h κ:ℝ}(hh:0<h)(hhH:h≤horizon)(hκ:0≤κ)(x y:HeatCircle):
    (matrix h κ x y-Matrix.diagonal (fun _:Fin 2=>κ*min (dist x y) (sqrt h)/128)).PosSemidef:=by
  let σ:Fin 2→ℝ:=fun _=>h
  let a:=centers x y
  let v:=weightedFeature σ σ a (fun _=>κ) measurable_const κ (fun _=>⟨hκ,le_rfl⟩) (fun _=>le_rfl) 0
  have hGram:Matrix.gram ℝ v=matrix h κ x y:=weightedFeature_gram σ σ a (fun _=>κ) measurable_const κ
    (fun _=>⟨hκ,le_rfl⟩) (fun _=>le_rfl) 0
  have hA:(matrix h κ x y).PosSemidef:=hGram▸Matrix.posSemidef_gram ℝ v
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨hA.1.sub (Matrix.isHermitian_diagonal _),?_⟩
  intro z
  let Z:WordRecursion.State 2:=WithLp.toLp 2 z
  have he:star z ⬝ᵥ (matrix h κ x y *ᵥ z)=
      κ*(∫s in Ici (0:ℝ),‖history h x y z s‖^2):=by
    have hi:=weightedHistory_integrable σ σ a (fun _=>κ) measurable_const κ
      (fun _=>⟨hκ,le_rfl⟩) (fun _=>le_rfl) 0 Z
    have hn:=weightedSynthesis_norm_sq σ σ a (fun _=>κ) measurable_const κ
      (fun _=>⟨hκ,le_rfl⟩) (fun _=>le_rfl) 0 Z
    rw [star_trivial,←Matrix.inner_toEuclideanCLM,←hGram,←featureSynthesis_inner,real_inner_self_eq_norm_sq]
    rw [hn,historyMeasure,integral_prod _ hi]
    simp_rw [integral_const_mul,realHistory_square_mass σ σ a (fun _=>le_rfl)]
    rfl
  have hb:=mul_le_mul_of_nonneg_left (history_lower hh hhH x y z) hκ
  rw [Matrix.sub_mulVec,dotProduct_sub,he]
  simp only [star_trivial,Matrix.mulVec_diagonal,dotProduct,Fin.sum_univ_two]
  nlinarith only [hb]

end SHE.NativeTwoPointCovariance
