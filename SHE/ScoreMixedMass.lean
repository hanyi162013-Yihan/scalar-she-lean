module
public import SHE.GeometricIntegral
public import SHE.GaussianMatrixScoreOrder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.ScoreMixedMass
open MeasureTheory GaussianIncrement MeasurableGaussianScores
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

/-- True score-mass and heat-row square mass yield the mixed fractional
mass. Covariance enlargement is allowed without any conditioning bound. -/
theorem bound (μ:Measure X) {A T:MeasurableGeneralizedInverse.Mat n}
    (hA:A.PosSemidef)(hT:T.PosSemidef)(hAT:(T-A).PosSemidef)
    (r:X→State n)(hr:Measurable r)(hrow:∀ᵐx∂μ,r x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) A).range)
    (hVi:Integrable (fun x=>scoreVariance A (r x)) μ)
    (i:Fin n)(hri:Integrable (fun x=>(r x i)^2) μ)
    {a b β:ℝ}(ha:0<a)(hb:0<b)(hβ:0≤β)(hβ2:β≤2)
    (hVa:(∫x,scoreVariance A (r x) ∂μ)≤a)(hrb:(∫x,(r x i)^2 ∂μ)≤b):
    Integrable (fun x=>scoreVariance T (r x)^(1-β/2)*|r x i|^β) μ ∧
      (∫x,scoreVariance T (r x)^(1-β/2)*|r x i|^β ∂μ)≤a^(1-β/2)*b^(β/2):=by
  let f:X→ℝ:=fun x=>max (scoreVariance T (r x)) 0
  let g:X→ℝ:=fun x=>(r x i)^2
  have hfm:Measurable f:=((scoreVariance_measurable.comp (measurable_const.prodMk hr)).max measurable_const)
  have hgm:Measurable g:=((EuclideanSpace.proj (𝕜:=ℝ) i).measurable.comp hr).pow_const 2
  have hf0:∀x,0≤f x:=fun x=>le_max_right _ _
  have hg0:∀x,0≤g x:=fun x=>sq_nonneg _
  have hfa:∀ᵐx∂μ,f x≤scoreVariance A (r x):=by
    filter_upwards [hrow] with x hx
    exact max_le (scoreVariance_antitone_matrix hA hT hAT hx) (scoreVariance_nonneg hA hx)
  have hfi:Integrable f μ:=hVi.mono' hfm.aestronglyMeasurable (by
    filter_upwards [hfa] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 x)] using hx)
  have hfb:(∫x,f x ∂μ)≤a:=(integral_mono_ae hfi hVi hfa).trans hVa
  have he:∀ᵐx∂μ,f x=scoreVariance T (r x):=by
    filter_upwards [hrow] with x hx
    have ht:r x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) T).range:=
      PositiveMatrixRanges.range_le_of_domination hT hA 1 (by simpa only [one_smul] using hAT) hx
    exact max_eq_left (scoreVariance_nonneg hT ht)
  have hgeom:=GeometricIntegral.positive_caps μ hfm hgm hf0 hg0 hfi hri ha hb
    (show 0≤1-β/2 by linarith) (show 0≤β/2 by linarith) (by ring) hfb hrb
  have hp (x:X):g x^(β/2)=|r x i|^β:=by
    dsimp only [g]
    rw [←sq_abs,←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  have hfun:(fun x=>f x^(1-β/2)*g x^(β/2))=ᵐ[μ]
      (fun x=>scoreVariance T (r x)^(1-β/2)*|r x i|^β):=by
    filter_upwards [he] with x hx
    rw [hx,hp]
  exact ⟨hgeom.1.congr hfun,(integral_congr_ae hfun).symm.le.trans hgeom.2⟩

end SHE.ScoreMixedMass
