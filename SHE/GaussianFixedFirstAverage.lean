module
public import SHE.WeightedAverageProduct
public import SHE.GaussianFirstSplit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.GaussianFixedFirstAverage
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution MeasurableGaussianScores
variable {X:Type*} [MeasurableSpace X] {n:ℕ}

def weight (R:MeasurableGeneralizedInverse.Mat n)(e:State n)(w:X→ℝ)(p:X×State n):ℝ:=
  w p.1*firstScore R e p.2
def shift (old:X→State n)(p:X×State n):State n:=old p.1+p.2

theorem score_measurable (R:MeasurableGeneralizedInverse.Mat n)(e:State n):Measurable (firstScore R e):=
  (innerSL ℝ (MeasurableGaussianScores.coefficient R e)).continuous.measurable
theorem weight_measurable (R:MeasurableGeneralizedInverse.Mat n)(e:State n){w:X→ℝ}(hw:Measurable w):
    Measurable (weight R e w):=(hw.comp measurable_fst).mul ((score_measurable R e).comp measurable_snd)
theorem weight_integrable (μ:Measure X)(R:MeasurableGeneralizedInverse.Mat n)(e:State n){w:X→ℝ}(hw:Integrable w μ):
    Integrable (weight R e w) (μ.prod (multivariateGaussian 0 R)):=
  hw.mul_prod (FiniteWordScores.firstScore_integrable R e)
theorem shift_measurable {old:X→State n}(hs:Measurable old):Measurable (shift old):=
  (hs.comp measurable_fst).add measurable_snd

/-- The fixed native FIRST score and every old weight form one genuine
product average. The full bounded Borel test is kept correlated. -/
theorem old_average (μ:Measure X) [SFinite μ] (R:MeasurableGeneralizedInverse.Mat n)(e:State n)
    (w:X→ℝ)(hw:Integrable w μ)(old:X→State n)(hs:Measurable old)
    (F:State n→ℝ)(hF:Measurable F)(M:ℝ)(hb:∀z,|F z|≤M)(z:State n):
    WeightedBorelAverage.average (multivariateGaussian 0 R) (firstScore R e) id
      (WeightedBorelAverage.average μ w old F) z=
    WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 R)) (weight R e w) (shift old) F z:=by
  have hi:=FiniteWordScores.firstScore_integrable R e
  rw [WeightedAverageProduct.commute (multivariateGaussian 0 R) μ (firstScore R e) w hi hw
    id old measurable_id hs F hF M hb]
  exact WeightedAverageProduct.product μ (multivariateGaussian 0 R) w (firstScore R e) hw hi
    old id hs measurable_id F hF M hb z

/-- Exact residual-law form of the native first-score integral. This
uses ordinary deterministic Fubini with actual integrable score weight. -/
theorem coefficient (μ:Measure X) [SFinite μ] (R B:MeasurableGeneralizedInverse.Mat n)(e:State n)
    (w:X→ℝ)(hw:Integrable w μ)(hwm:Measurable w)(old:X→State n)(hs:Measurable old)
    (F:State n→ℝ)(hF:Measurable F)(M:ℝ)(hM:0≤M)(hb:∀z,|F z|≤M)(z:State n):
    (∫y,∫r,WeightedBorelAverage.average μ w old F (z+y+r)*firstScore R e y
      ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R)=
    gaussianAverage B (WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 R))
      (weight R e w) (shift old) F) z:=by
  let G:=WeightedBorelAverage.average μ w old F
  have hg:Measurable G:=WeightedBorelAverage.measurable μ w hwm old hs F hF
  have hbG:∀z,|G z|≤M*∫x,|w x| ∂μ:=WeightedBorelAverage.bound μ w hw old hs F hF M hM hb
  calc
    _=WeightedBorelAverage.average (multivariateGaussian 0 R) (firstScore R e) id (gaussianAverage B G) z:=by
      change (∫y,∫r,G (z+y+r)*firstScore R e y ∂multivariateGaussian 0 B ∂multivariateGaussian 0 R)=
        ∫y,firstScore R e y*(∫r,G (z+id y+r) ∂multivariateGaussian 0 B) ∂multivariateGaussian 0 R
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_mul_const]
      simp only [id_eq]
      ring
    _=gaussianAverage B (WeightedBorelAverage.average (multivariateGaussian 0 R) (firstScore R e) id G) z:=by
      simpa only [WeightedBorelAverage.average,gaussianAverage,one_mul,id_eq] using
        WeightedAverageProduct.commute (multivariateGaussian 0 R) (multivariateGaussian 0 B)
          (firstScore R e) (fun _=>1) (FiniteWordScores.firstScore_integrable R e) (integrable_const 1)
          id id measurable_id measurable_id G hg (M*∫x,|w x| ∂μ) hbG z
    _=_:=by
      unfold gaussianAverage
      apply integral_congr_ae
      filter_upwards with r
      exact old_average μ R e w hw old hs F hF M hb (z+r)

/-- Scalar directional derivative of the original Gaussian kernel has
an EXACT fixed native-score product representation, even for singular
covariances and merely bounded Borel whole tests. -/
theorem hasDerivAt (μ:Measure X) [SFinite μ] {R B:MeasurableGeneralizedInverse.Mat n}
    (hR:R.PosSemidef)(hB:B.PosSemidef){e:State n}(he:e∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)
    (w:X→ℝ)(hw:Integrable w μ)(hwm:Measurable w)(old:X→State n)(hs:Measurable old)
    (F:State n→ℝ)(hF:Measurable F)(M:ℝ)(hM:0≤M)(hb:∀z,|F z|≤M)(z:State n)(θ:ℝ):
    HasDerivAt (fun t:ℝ=>gaussianAverage (R+B) (WeightedBorelAverage.average μ w old F) (z+t•e))
      (gaussianAverage B (WeightedBorelAverage.average (μ.prod (multivariateGaussian 0 R))
        (weight R e w) (shift old) F) (z+θ•e)) θ:=by
  have hh:=GaussianFirstSplit.hasDerivAt_split hR hB he
    (WeightedBorelAverage.measurable μ w hwm old hs F hF) (M*∫x,|w x| ∂μ)
    (WeightedBorelAverage.bound μ w hw old hs F hF M hM hb) z θ
  rw [coefficient μ R B e w hw hwm old hs F hF M hM hb (z+θ•e)] at hh
  exact hh
end SHE.GaussianFixedFirstAverage
