module
public import SHE.PhysicalHessianChain
public import SHE.ScalarPhysicalRootHolder
public import SHE.IntervalScoreHolderMass

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
namespace SHE.PhysicalChainArrays
open Set MeasureTheory ProbabilityTheory AddCircle GaussianAudit StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain ProjectedUncutWord
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
local instance physicalFreshMassChain_period : Fact (0<2*Real.pi):=⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance oldAverage WordRecursion.covariance
  scoreVariance WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} (L:Level R X 1)

/-- Fresh collision improvement pointwise on a genuine physical chain.
This form permits random-past substitution on the already checked
common chain event. All bounds are independent of coefficient derivatives. -/
theorem hessian_holder_mass_of_chain (c:Domain→ℝ)(hc:Measurable c)
    {ell A B H Hr β:ℝ}(hell:0<ell)(hR:∀p,ell≤R.reference p)
    (hA:0≤A)(hB:0≤B)(hH:0≤H)(hHr:0≤Hr)(hβ:0≤β)(hβ2:β≤2)
    (ha:∀z,|R.totalVariance z|≤A)(hroot:∀p z,|L.test p z|≤B)
    (hh:∀s t,|R.totalVariance s-R.totalVariance t|≤H*|s-t|^β)
    (hrootmod:∀p z w,|L.test p z-L.test p w|≤Hr*|z 0-w 0|^β)
    (hages:∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (k:ℕ)(p:History X k)(chain:Chain L k p (fun i=>i))(hs:chain.CoordinateSupport)
    (hp:Physical L ((carrier L k).observations.observations p) c chain)
    (q:ℝ)(hq:0≤q)(hqt:q<(carrier L k).terminal p)(hgap1:(carrier L k).terminal p-q≤1)
    (z:WordRecursion.State (1+k)):
    Integrable (fun x:HeatCircle=>WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z (heatRow ((carrier L k).observations.observations p) q x)) haarAddCircle ∧
    (∫x:HeatCircle,|WordRecursion.directionalSecond
      (gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z (heatRow ((carrier L k).observations.observations p) q x)| ∂haarAddCircle)≤
      (1+B+(A+R.upper)/2)^(k+1)*oldAbsoluteMass L c k p*secondScoreAbsIncrementMoment β*
        (Hr+(k:ℝ)*H/2)*IntervalScoreHolderMass.constant (1+k) ell β*
          ((carrier L k).terminal p-q)^(β/4-1) := by
  let Z:=(carrier L k).observations.observations p
  let hi:=(carrier L k).terminal p
  let C:=WordRecursion.covariance R.reference Z q hi
  let T:=fullResidualCovariance L c k p q
  let row:=heatRow Z q
  let V:=fun x:HeatCircle=>scoreVariance T (row x)
  let F:=fun (i:Fin (1+k))(x:HeatCircle)=>V x^(1-β/2)*|row x i|^β
  let root:Fin (1+k):=rootSelector k (fun i=>i) 0
  let Cw:=(1+B+(A+R.upper)/2)^(k+1)*oldAbsoluteMass L c k p*secondScoreAbsIncrementMoment β
  let J:=fun x:HeatCircle=>Hr*F root x+H/2*(∑j:Fin k,F (leafIndex k (fun i=>i) j) x)
  let Mx:=IntervalScoreHolderMass.constant (1+k) ell β*(hi-q)^(β/4-1)
  have hZ:∀i,(Z i).stop≤(Z i).target:=RecursiveScoreSupport.carrier_ages L hages k p
  have hstop:∀i,hi≤(Z i).stop:=(carrier L k).stops_after p
  have hrowm:Measurable row:=(HeatRowWeighted.heatRow_vector_measurable Z).comp
    (measurable_const.prodMk measurable_id)
  have hdata:=fresh_row_score_mass_of_chain L c hell hR hages k p chain hp q hq hqt
  have hT:T.PosSemidef:=hdata.1
  have hrange:∀ᵐx:HeatCircle∂haarAddCircle,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
    hdata.2.1.mono (fun _ hx=>hx.1)
  have hmixed(i:Fin (1+k)):Integrable (F i) haarAddCircle ∧ (∫x,F i x ∂haarAddCircle)≤Mx:=by
    have hsq:=StoppedRowSquareMass.coordinate_bound (fun i=>(Z i).stop) (fun i=>(Z i).target)
      (fun i=>(Z i).center) hZ hqt hgap1 (fun i=>Or.inr (hstop i)) i
    have hrow(x:HeatCircle):stoppedRow (fun i=>(Z i).stop) (fun i=>(Z i).target)
        (fun i=>(Z i).center) (q,x)=row x:=by
      ext i
      simp only [stoppedRow,row,heatRow,ite_eq_left (hqt.trans_le (hstop i))]
    simp only [hrow] at hsq
    have hden:0<ell*(hi-q):=mul_pos hell (sub_pos.mpr hqt)
    have hcap:(∫x,V x ∂haarAddCircle)≤(((1+k:ℕ):ℝ)+1)/(ell*(hi-q)):=
      hdata.2.2.2.trans (div_le_div_of_nonneg_right (by linarith) hden.le)
    obtain ⟨hfi,hfb⟩:=ScoreMixedMass.bound haarAddCircle hT hT (by
      simpa only [sub_self] using (Matrix.PosSemidef.zero : (0:Matrix (Fin (1+k)) (Fin (1+k)) ℝ).PosSemidef))
      row hrowm hrange hdata.2.2.1 i hsq.1
      (div_pos (by positivity) hden)
      (mul_pos (by linarith [StoppedFourier.heatConstant_pos]) (Real.rpow_pos_of_pos (sub_pos.mpr hqt) _))
      hβ hβ2 hcap hsq.2
    rw [IntervalScoreHolderMass.power_identity hell (sub_pos.mpr hqt) (1+k)] at hfb
    exact ⟨hfi,hfb⟩
  have hCw:0≤Cw:=by
    have hRu:=R.upper_nonneg
    have hscore:0≤secondScoreAbsIncrementMoment β:=integral_nonneg (fun _=>by positivity)
    exact mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (oldAbsoluteMass_nonneg L c k p)) hscore
  have hbound:∀ᵐx:HeatCircle∂haarAddCircle,
      |WordRecursion.directionalSecond (gaussianAverage C (UncutSmoothWords.test L k p)) z (row x)|≤Cw*J x:=by
    filter_upwards [hrange] with x hx
    have hK:0≤Hr*|row x root|^β:=mul_nonneg hHr (Real.rpow_nonneg (abs_nonneg _) _)
    have hh:=hessian_holder_of_chain L c hc hell hR hA hB hH hK hβ ha hroot hh hages
      k p chain hs hp q hq hqt (row x) z hx
        (initial_directional_holder L hrootmod k p (fun i=>i) (row x))
    have he:(wordHolderCost (R:=R) A B H (Hr*|row x root|^β) β k p (row x)*oldAbsoluteMass L c k p)*
        secondScoreAbsIncrementMoment β*V x^(1-β/2)=Cw*J x:=by
      dsimp only [wordHolderCost,Cw,J,F]
      rw [←Finset.mul_sum]
      ring
    exact hh.trans_eq he
  have hJi:Integrable J haarAddCircle:=((hmixed root).1.const_mul Hr).add
    ((integrable_finsetSum _ (fun j _=>(hmixed (leafIndex k (fun i=>i) j)).1)).const_mul (H/2))
  have hJb:(∫x,J x ∂haarAddCircle)≤(Hr+(k:ℝ)*H/2)*Mx:=by
    dsimp only [J]
    rw [integral_add ((hmixed root).1.const_mul Hr)
      ((integrable_finsetSum _ (fun j _=>(hmixed (leafIndex k (fun i=>i) j)).1)).const_mul (H/2)),
      integral_const_mul,integral_const_mul,integral_finsetSum _ (fun j _=>(hmixed (leafIndex k (fun i=>i) j)).1)]
    have hsum:(∑j:Fin k,∫x,F (leafIndex k (fun i=>i) j) x ∂haarAddCircle)≤(k:ℝ)*Mx:=by
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=Finset.univ) (fun j _=>(hmixed (leafIndex k (fun i=>i) j)).2)
    exact (add_le_add (mul_le_mul_of_nonneg_left (hmixed root).2 hHr)
      (mul_le_mul_of_nonneg_left hsum (show 0≤H/2 from by positivity))).trans_eq (by ring)
  have hm:Measurable (fun x:HeatCircle=>WordRecursion.directionalSecond
      (gaussianAverage C (UncutSmoothWords.test L k p)) z (row x)):=by
    unfold WordRecursion.directionalSecond
    have he₁:Continuous (fun p:(WordRecursion.State (1+k)→L[ℝ]WordRecursion.State (1+k)→L[ℝ]ℝ)×
        WordRecursion.State (1+k)=>p.1 p.2):=continuous_fst.clm_apply continuous_snd
    have he₂:Continuous (fun p:(WordRecursion.State (1+k)→L[ℝ]ℝ)×WordRecursion.State (1+k)=>p.1 p.2):=
      continuous_fst.clm_apply continuous_snd
    exact he₂.measurable.comp ((he₁.measurable.comp
      (measurable_const.prodMk hrowm)).prodMk hrowm)
  have hiH:Integrable (fun x:HeatCircle=>WordRecursion.directionalSecond
      (gaussianAverage C (UncutSmoothWords.test L k p)) z (row x)) haarAddCircle:=
    (hJi.const_mul Cw).mono' hm.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hiH,?_⟩
  have hiB:=integral_mono_ae hiH.abs (hJi.const_mul Cw) hbound
  rw [integral_const_mul] at hiB
  exact hiB.trans ((mul_le_mul_of_nonneg_left hJb hCw).trans_eq (by dsimp only [Cw,Mx,hi];ring))

end SHE.PhysicalChainArrays
