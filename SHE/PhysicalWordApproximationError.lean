module

public import SHE.PhysicalWordHessianMass
public import SHE.ApproximateCoefficientInsertion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers StoppedGaussianFeatures GaussianConvolution
open ApproximateCoefficientInsertion SmoothApproximation ScalarData
local instance physicalWordApproximationError_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] fullResidualCovariance oldAverage WordRecursion.covariance
  MeasurableGaussianScores.scoreVariance MeasurableGeneralizedInverse.generalizedInverse
  WordRecursion.directionalSecond GaussianConvolution.gaussianAverage UncutSmoothWords.test
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ} (L : Level R X n)

def approximationError (D : ScalarData) (j k : ℕ) (p : History X k)
    (field : Domain→ℝ) (q : ℝ) (z : WordRecursion.State (n+k)) (x : HeatCircle) : ℝ :=
  (1/2:ℝ)*(originalTotal D (field (q,x))-smoothTotal D j (field (q,x)))*
    WordRecursion.directionalSecond (gaussianAverage (WordRecursion.covariance R.reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) z (heatRow ((carrier L k).observations.observations p) q x)

/-- The actual deep-word approximation insertion, with the newest
physical factor OUTSIDE every Gaussian average. Its uniform cap has no
derivatives of the approximating coefficient and only one inverse fresh
gap. A positive gap cutoff may therefore be fixed before the smoothing
index is selected. -/
theorem actual_approximation_error_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell ellR A B : ℝ} (hell : 0<ell) (hb : ∀p,ell≤c p ∧ c p≤R.reference p)
    (hellR : 0<ellR) (hR : ∀p,ellR≤R.reference p)
    (hA : 0≤A) (hB : 0≤B) (ha : ∀z,|R.totalVariance z|≤A)
    (hroot : ∀p z,|L.test p z|≤B)
    (hages : ∀p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) (D : ScalarData) (j : ℕ) :
    ∀ᵐ p∂CutoffWordHistories.historyMeasure R μ k,
      ∀q:ℝ,0≤q→q<(carrier L k).terminal p→
      ∀field:Domain→ℝ,Measurable field→∀z:WordRecursion.State (n+k),
      Integrable (approximationError L D j k p field q z) haarAddCircle ∧
      |∫x:HeatCircle,approximationError L D j k p field q z x ∂haarAddCircle|≤
        ScalarApproximationDiscrepancy.scalarError D j*
          (((B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p)*((n+k:ℕ):ℝ)/
            (ellR*((carrier L k).terminal p-q))) := by
  filter_upwards [actual_hessian_mass_ae L c hc hell hb hellR hR hA hB ha hroot hages μ k] with p hp
  intro q hq hqt field hfield z
  obtain ⟨hi,hbH⟩:=hp q hq hqt z
  let H:=fun x:HeatCircle=>WordRecursion.directionalSecond
    (gaussianAverage (WordRecursion.covariance R.reference
      ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p)) z (heatRow ((carrier L k).observations.observations p) q x)
  let ε:=ScalarApproximationDiscrepancy.scalarError D j
  have hε:0≤ε:=ScalarApproximationDiscrepancy.scalarError_nonneg D j
  have htotal:Measurable (originalTotal D):=by
    have he:originalTotal D=(fun x=>(ScalarReduction.additiveAmplitude D.lower)^2+D.residualCoefficient x):=
      funext (fun x=>(D.variance_split x).symm)
    rw [he]
    exact measurable_const.add D.residual_continuous.measurable
  have hsmooth:Measurable (smoothTotal D j):=
    measurable_const.add (D.smooth_boundedSmooth j).smooth.continuous.measurable
  have hcoef:Measurable (fun x:HeatCircle=>(1/2:ℝ)*(originalTotal D (field (q,x))-smoothTotal D j (field (q,x)))):=
    ((htotal.comp (hfield.comp (measurable_const.prodMk measurable_id))).sub
      (hsmooth.comp (hfield.comp (measurable_const.prodMk measurable_id)))).const_mul _
  have hcpoint(x:HeatCircle):|(1/2:ℝ)*(originalTotal D (field (q,x))-smoothTotal D j (field (q,x)))|≤ε/2:=by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    nlinarith [total_error D j (field (q,x))]
  have hiE:Integrable (approximationError L D j k p field q z) haarAddCircle:=by
    exact hi.bdd_mul hcoef.aestronglyMeasurable (ae_of_all _ (fun x=>by
      simpa only [Real.norm_eq_abs] using hcpoint x))
  have hpoint(x:HeatCircle):|approximationError L D j k p field q z x|≤(ε/2)*|H x|:=by
    unfold approximationError
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hcpoint x) (abs_nonneg _)
  refine ⟨hiE,?_⟩
  calc
    _≤∫x:HeatCircle,|approximationError L D j k p field q z x| ∂haarAddCircle:=by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (approximationError L D j k p field q z) (μ:=haarAddCircle))
    _≤∫x:HeatCircle,(ε/2)*|H x| ∂haarAddCircle:=
      integral_mono hiE.norm (hi.norm.const_mul (ε/2)) hpoint
    _=(ε/2)*(∫x:HeatCircle,|H x| ∂haarAddCircle):=integral_const_mul _ _
    _≤(ε/2)*((2*((B*((A+R.upper)/2)^k)*oldAbsoluteMass L c k p))*
        ((n+k:ℕ):ℝ)/(ellR*((carrier L k).terminal p-q))):=
      mul_le_mul_of_nonneg_left hbH (div_nonneg hε (by norm_num))
    _=_:=by dsimp only [ε];ring

end SHE.PhysicalChainArrays
