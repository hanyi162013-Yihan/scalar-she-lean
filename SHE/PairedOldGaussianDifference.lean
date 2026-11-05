module

public import SHE.PairedGaussianComparison
public import SHE.NoFreshGaussianIdentity
public import SHE.AssignmentGapPartition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.PairedOldGaussianDifference
open Set MeasureTheory ProbabilityTheory GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
  GaussianVectorFractions StoppedFourier GaussianConvolution
open scoped BigOperators ContDiff
open Classical
variable {n r m:ℕ}

/-- Full old-score Gaussian comparison at a common future law. Every
assignment and normalized paired slot is explicit; no artificial fresh
score is inserted, and both own baselines remain in the formula. -/
theorem difference (P:CanonicalCovariance.ProfileParameters)
    (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (hA:∀j,(A j).PosSemidef)
    (D:Fin r→State n) (hD:∀j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range)
    (B:Matrix (Fin n) (Fin n) ℝ) (F:State 1→ℝ) (hF:ContDiff ℝ ∞ F)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n)
    (newMean oldMean:State n) (newBaseline oldBaseline:Fin m→ℝ)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hb:∀j,j≤r+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j):
    let old:=fun bas=>WeightedBorelAverage.average
      (Measure.pi (fun j=>multivariateGaussian (0:State n) (A j)))
      (fun x=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (x j))
      (fun x=>∑j,x j) (VectorAssignmentIdentity.raw P.coefficient F g leaf bas)
    let μG:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)
    gaussianAverage B (old newBaseline) newMean-gaussianAverage B (old oldBaseline) oldMean=
      ((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
        ∑i,PairedAssignedTelescope.sources P choices g leaf newMean oldMean newBaseline oldBaseline ν χ i*
          (∫x,PairedAssignedTelescope.slot P A D choices F g leaf newMean oldMean newBaseline oldBaseline ν χ i x ∂μG))).sum:=by
  intro old μG
  have hF0(z):|F z|≤A0:=by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,mul_one] using hb 0 (by omega) z
  have ha(z):|P.coefficient z|≤P.upper:=by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hn:=NoFreshGaussianIdentity.full_average_eq A hA D hD B (List.finRange r)
    (List.nodup_finRange r) P.coefficient P.measurable F hF.continuous.measurable g leaf
    newBaseline hA0 hF0 ha newMean
  have ho:=NoFreshGaussianIdentity.full_average_eq A hA D hD B (List.finRange r)
    (List.nodup_finRange r) P.coefficient P.measurable F hF.continuous.measurable g leaf
    oldBaseline hA0 hF0 ha oldMean
  rw [hn,ho]
  have hsub (cs:List (List (Fin r×Fin (m+1)))):
      (cs.map (fun c=>∫x,NoFreshGaussianIdentity.value A D c P.coefficient F g leaf newBaseline newMean x ∂μG)).sum-
      (cs.map (fun c=>∫x,NoFreshGaussianIdentity.value A D c P.coefficient F g leaf oldBaseline oldMean x ∂μG)).sum=
      (cs.map (fun c=>(∫x,NoFreshGaussianIdentity.value A D c P.coefficient F g leaf newBaseline newMean x ∂μG)-
        (∫x,NoFreshGaussianIdentity.value A D c P.coefficient F g leaf oldBaseline oldMean x ∂μG))).sum:=by
    induction cs with
    | nil=>simp
    | cons c cs ih=>simp only [List.map_cons,List.sum_cons];rw [←ih];ring
  rw [hsub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs hcs
  have hnd:=AssignmentGapPartition.coordinates_nodup cs hcs
  have hlen:(block cs 0).length≤r:=by
    simpa only [Fintype.card_fin] using (GaussianAssignmentBlocks.block_nodup cs hnd 0).length_le_card
  exact (PairedAssignedTelescope.gaussian_difference P A D B cs hnd F g leaf newMean oldMean
    newBaseline oldBaseline hA0 hν hχ hχβ (hF.of_le (by simp))
    (fun j hj=>hb j (hj.trans (by omega)))).2

end SHE.PairedOldGaussianDifference
