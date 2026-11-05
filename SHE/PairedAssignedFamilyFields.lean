module

public import SHE.PairedGaussianComparison
public import SHE.GaussianFibreBorel
public import SHE.VaryingAssignedFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section
namespace SHE.PairedAssignedTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianVectorFractions
open scoped BigOperators
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {W:Type*} [MeasurableSpace W] {n r m d:ℕ}

theorem parameter_differences_measurable (is:List (Fin r))
    (F:W×(Fin r→State n)→ℝ) (hF:Measurable F):
    Measurable (fun z:W×(Fin r→State n)=>fractionDifferences is (fun y=>F (z.1,y)) z.2) := by
  induction is with
  | nil => exact hF
  | cons i is ih =>
    change Measurable (fun z:W×(Fin r→State n)=>
      fractionDifferences is (fun y=>F (z.1,y)) z.2-
        fractionDifferences is (fun y=>F (z.1,y)) (Function.update z.2 i 0))
    have ht:Measurable (fun z:W×(Fin r→State n)=>(z.1,Function.update z.2 i 0)):=by fun_prop
    exact ih.sub (ih.comp ht)

/-- The actual assigned root stays jointly Borel when the ROOT TEST,
its initial parameter, current mean, and covariance rank all vary. -/
theorem root_family_measurable (choices:List (Fin r×Fin (m+1)))
    (F:W→State d→ℝ) (hF:Measurable (Function.uncurry F))
    (mean:W→State n) (hm:Measurable mean) (g:Fin d→Fin n):
    Measurable (fun z:W×((Fin r→State n)×State n)=>
      VectorControlledRoot.value choices 0 (F z.1) (mean z.1) g z.2) := by
  let raw:(W×State n)×(Fin r→State n)→ℝ:=fun z=>
    F z.1.1 (VectorRootClips.affineSum (GaussianCoordinates.projection g (mean z.1.1+z.1.2))
      (fun _ : Fin r=>GaussianCoordinates.projection g) z.2)
  have hr:Measurable raw:=by
    have hp:Measurable (fun z:(W×State n)×(Fin r→State n)=>
        (z.1.1,VectorRootClips.affineSum (GaussianCoordinates.projection g (mean z.1.1+z.1.2))
          (fun _ : Fin r=>GaussianCoordinates.projection g) z.2)):=by
      apply measurable_fst.fst.prodMk
      unfold VectorRootClips.affineSum
      fun_prop
    convert! hF.comp hp using 1
  have hh:=parameter_differences_measurable (block choices 0) raw hr
  have hp:Measurable (fun z:W×((Fin r→State n)×State n)=>
      ((z.1,z.2.2),suppress (suppressed choices 0) z.2.1)):=
    (measurable_fst.prodMk measurable_snd.snd).prodMk
      ((measurable_suppress _).comp measurable_snd.fst)
  convert! hh.comp hp using 1

theorem slot_family_measurable (P:CanonicalCovariance.ProfileParameters)
    (A:W→Fin r→Matrix (Fin n) (Fin n) ℝ) (hA:∀j,Measurable (fun w=>A w j))
    (D:W→Fin r→State n) (hD:∀j,Measurable (fun w=>D w j))
    (choices:List (Fin r×Fin (m+1))) (F:W→State 1→ℝ) (hF:Measurable (Function.uncurry F))
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:W→State n)
    (hn:Measurable newMean) (ho:Measurable oldMean)
    (newBaseline oldBaseline:W→Fin m→ℝ)
    (hbn:∀j,Measurable (fun w=>newBaseline w j)) (hbo:∀j,Measurable (fun w=>oldBaseline w j))
    (ν χ:ℝ) (i:Fin (m+1)):
    Measurable (fun z:W×((Fin r→State n)×State n)=>
      slot P (A z.1) (D z.1) choices (F z.1) g leaf (newMean z.1) (oldMean z.1)
        (newBaseline z.1) (oldBaseline z.1) ν χ i z.2) := by
  have hfac(mean:W→State n)(hm:Measurable mean)(bas:W→Fin m→ℝ)
      (hbas:∀j,Measurable (fun w=>bas w j))(j:Fin (m+1)):
      Measurable (fun z:W×((Fin r→State n)×State n)=>
        AssignedCurrentTelescope.factor P.coefficient choices (F z.1) (mean z.1) g leaf (bas z.1) z.2 j):=by
    refine Fin.cases (root_family_measurable choices F hF mean hm g) (fun j=>?_) j
    exact VaryingAssignedFields.leaf_measurable choices j.succ P.coefficient P.measurable
      mean hm (leaf j) (fun w=>bas w j) (hbas j)
  have hs(j:Fin (m+1)):Measurable (fun w=>sources P choices g leaf (newMean w) (oldMean w)
      (newBaseline w) (oldBaseline w) ν χ j):=by
    refine Fin.cases ?_ (fun j=>?_) j
    · unfold sources
      simp only [Fin.cases_zero]
      have hp:Measurable (fun w=>GaussianCoordinates.projection g (newMean w-oldMean w)):=by fun_prop
      exact (measurable_const.min (measurable_const.mul hp.norm)).pow_const χ
    · simp only [sources,Fin.cases_succ,PairedRoughWordMoments.source]
      have hmn:Measurable (fun w=>newMean w (leaf j)):=
        (EuclideanSpace.proj (𝕜:=ℝ) (leaf j)).continuous.measurable.comp hn
      have hmo:Measurable (fun w=>oldMean w (leaf j)):=
        (EuclideanSpace.proj (𝕜:=ℝ) (leaf j)).continuous.measurable.comp ho
      split_ifs
      · unfold NormalizedPairedLeaf.source
        exact ((continuous_abs.measurable.comp (hmn.sub hmo)).pow_const χ).const_mul _ |>.add
          ((continuous_abs.measurable.comp ((hbn j).sub (hbo j))).pow_const _)
      · exact (continuous_abs.measurable.comp (hmn.sub hmo)).pow_const χ
  have hscore(j:Fin r):Measurable (fun z:W×((Fin r→State n)×State n)=>
      MeasurableGaussianScores.secondScore (A z.1 j) (D z.1 j) (z.2.1 j)):=by
    have hp:Measurable (fun z:W×((Fin r→State n)×State n)=>((A z.1 j,D z.1 j),z.2.1 j)):=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk
        ((measurable_pi_apply j).comp measurable_snd.fst)
    convert! MeasurableGaussianScores.secondScore_measurable.comp hp using 1
  unfold slot NormalizedProductTelescope.term
  exact (Finset.measurable_prod _ (fun j _=>hscore j)).mul
    (((NormalizedScalarMoment.measurable _ _
      ((hfac newMean hn newBaseline hbn i).sub (hfac oldMean ho oldBaseline hbo i))
      ((hs i).comp measurable_fst)).mul
        (Finset.measurable_prod _ (fun j _=>hfac oldMean ho oldBaseline hbo j))).mul
          (Finset.measurable_prod _ (fun j _=>hfac newMean hn newBaseline hbn j)))

/-- Changing-rank Gaussian averages of the ACTUAL normalized telescope
slot are jointly Borel in all original history and past-state parameters. -/
theorem slot_average_family_measurable (P:CanonicalCovariance.ProfileParameters)
    (A:W→Fin r→Matrix (Fin n) (Fin n) ℝ) (hA:∀j,Measurable (fun w=>A w j))
    (B:W→Matrix (Fin n) (Fin n) ℝ) (hB:Measurable B)
    (D:W→Fin r→State n) (hD:∀j,Measurable (fun w=>D w j))
    (choices:List (Fin r×Fin (m+1))) (F:W→State 1→ℝ) (hF:Measurable (Function.uncurry F))
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:W→State n)
    (hn:Measurable newMean) (ho:Measurable oldMean)
    (newBaseline oldBaseline:W→Fin m→ℝ)
    (hbn:∀j,Measurable (fun w=>newBaseline w j)) (hbo:∀j,Measurable (fun w=>oldBaseline w j))
    (ν χ:ℝ) (i:Fin (m+1)):
    Measurable (fun w=>∫x,slot P (A w) (D w) choices (F w) g leaf (newMean w) (oldMean w)
      (newBaseline w) (oldBaseline w) ν χ i x
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A w j))).prod
        (multivariateGaussian (0:State n) (B w))) :=
  GaussianFibreBorel.average_measurable A hA B hB _
    (slot_family_measurable P A hA D hD choices F hF g leaf newMean oldMean hn ho
      newBaseline oldBaseline hbn hbo ν χ i)

end SHE.PairedAssignedTelescope
