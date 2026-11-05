module

public import SHE.GaussianCoarseSecondScore
public import SHE.RootCovarianceSums

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.FiniteWordScores
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianConvolution MeasurableGaussianScores
open scoped BigOperators
variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- Finite covariance-mark linearity needs no covariance range or rank
assumption: ordinary physical row energy suffices for applicability. -/
theorem covarianceMark_finset_unconditional (μ : Measure X) (A : Matrix (Fin n) (Fin n) ℝ)
    (e : X→ℝ) (he : Measurable e) (row : X→State n) (hr : Measurable row)
    (henergy : Integrable (fun x=>|e x| * ‖row x‖^2) μ)
    (F : ℕ→State n→ℝ) (hF : ∀ j,Measurable (F j)) (B : ℕ→ℝ)
    (hb : ∀ j z,|F j z|≤B j) (s : Finset ℕ) (m : State n) :
    covarianceMark μ A e row (fun z=>∑ j∈s,F j z) m=
      ∑ j∈s,covarianceMark μ A e row (F j) m := by
  have hi (j : ℕ) (x : X) : Integrable
      (fun y=>F j (m+y)*secondScore A (row x) y) (multivariateGaussian 0 A) :=
    (GaussianVectorFractions.gaussian_secondScore_integrable A (row x)).bdd_mul
      ((hF j).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (ae_of_all _ (fun y=>by simpa only [Real.norm_eq_abs] using hb j (m+y)))
  have ho (j : ℕ) : Integrable
      (fun x=>e x*(∫ y,F j (m+y)*secondScore A (row x) y ∂multivariateGaussian 0 A)) μ :=
    GaussianCoarseSecondScore.rawMark_outer_integrable μ A row hr e he henergy (F j) (hF j) (B j) (hb j) m
  unfold covarianceMark
  simp_rw [Finset.sum_mul]
  simp_rw [integral_finsetSum s (fun j _=>hi j _),Finset.mul_sum]
  rw [integral_finsetSum s (fun j _=>ho j),Finset.mul_sum]
end SHE.FiniteWordScores

namespace SHE.RootFiniteSums
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  SmoothCylinders UniformSmooth PhysicalScoreChain PhysicalChainArrays RootSmoothSums GaussianConvolution CoveredControlledLaw
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)
variable (F : ℕ→X→WordRecursion.State n→ℝ) (hF : ∀ j,UniformBoundedSmooth (F j))
  (hFm : ∀ j,Measurable (fun z : X×WordRecursion.State n=>F j z.1 z.2))
local notation "B"=>band L F hF hFm
local notation "S"=>sumLevel L F hF hFm
attribute [local irreducible] PhysicalChainArrays.oldAverage PhysicalChainArrays.fullResidualCovariance
  FiniteWordScores.covarianceMark MeasurableGaussianScores.coefficient MeasurableGeneralizedInverse.generalizedInverse

theorem covariance_point_sum_unconditional (s : Finset ℕ) (c e : StoppedGaussianFeatures.Domain→ℝ)
    (hc : Measurable c) (he : Measurable e) (k : ℕ) (q : ℝ)
    (m : WordRecursion.State (n+k)) (p : History X k)
    (henergy : Integrable (fun z=>|e z| *
      ‖StoppedGaussianFeatures.stoppedRow (stops L k p) (targets L k p) (centers L k p) z‖^2)
      (StoppedGaussianFeatures.historyMeasure q)) :
    ActualCovarianceMarkFields.point (S s) c e k q m p=
      ∑ j∈s,ActualCovarianceMarkFields.point (B j) c e k q m p := by
  classical
  simp only [sumLevel,band,covariance_point_withRoot L]
  by_cases hq : q<(carrier L k).terminal p
  · simp only [if_pos hq]
    change FiniteWordScores.covarianceMark _ _ e _ (oldAverage (S s) c k p) m=
      ∑ j∈s,FiniteWordScores.covarianceMark _ _ e _ (oldAverage (B j) c k p) m
    rw [oldAverage_sum L F hF hFm s c k p]
    have hf : (∑ j∈s,oldAverage (B j) c k p)=fun z=>∑ j∈s,oldAverage (B j) c k p z:=by
      funext z
      simp only [Finset.sum_apply]
    rw [hf]
    choose C hC hcb using fun j=>oldAverage_bounded (B j) c k p
    have hm (j : ℕ) : Measurable (oldAverage (B j) c k p):=
      (oldAverage_measurable (B j) c hc k).comp
        (measurable_const.prodMk (measurable_id : Measurable (id : WordRecursion.State (n+k)→_)))
    exact FiniteWordScores.covarianceMark_finset_unconditional _ _ e he _
      (StoppedGaussianFeatures.stoppedRow_measurable _ _ _) henergy
      (fun j=>oldAverage (B j) c k p) hm C hcb s m
  · simp only [if_neg hq,Finset.sum_const_zero]
end SHE.RootFiniteSums
