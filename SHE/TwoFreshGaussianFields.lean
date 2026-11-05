module

public import SHE.TwoFreshVaryingMoments
public import SHE.GaussianFibreBorel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.TwoFreshGaussianFields
open MeasureTheory ProbabilityTheory GaussianIncrement GaussianDependentScores GaussianScoreKernel
  MeasurableGaussianScores
variable {Ω:Type*} [MeasurableSpace Ω] {n d r m:ℕ}

/-- Borel integration over the actual THREE changing Gaussian laws.
Both fresh fractions and every old covariance may change rank together. -/
theorem average_measurable
    (A:Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,Measurable (fun ω=>A ω j))
    (R C:Ω→MeasurableGeneralizedInverse.Mat n) (hR:Measurable R) (hC:Measurable C)
    (F:Ω×((Fin r→State n)×(State n×State n))→ℝ) (hF:Measurable F):
    Measurable (fun ω=>∫x,F (ω,x)
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
        ((multivariateGaussian (0:State n) (R ω)).prod (multivariateGaussian (0:State n) (C ω)))):=by
  let κold:=FiniteKernelProduct.kernel r (fun j=>gaussianKernel (fun ω=>A ω j) (hA j))
  let κ:=κold.prod ((gaussianKernel R hR).prod (gaussianKernel C hC))
  have hh:=(hF.stronglyMeasurable.integral_kernel_prod_right' (κ:=κ)).measurable
  convert! hh using 1
  funext ω
  rw [show κ ω=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
      ((multivariateGaussian (0:State n) (R ω)).prod (multivariateGaussian (0:State n) (C ω))) by
    dsimp only [κ]
    rw [Kernel.prod_apply,Kernel.prod_apply,FiniteKernelProduct.kernel_apply]
    rfl]

/-- The complete two-fresh assigned Gaussian word is Borel under fully
dependent covariance, direction, current-mean and baseline fields. -/
theorem word_average_measurable
    (A:Ω→Fin r→MeasurableGeneralizedInverse.Mat n) (hA:∀j,Measurable (fun ω=>A ω j))
    (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (R C:Ω→MeasurableGeneralizedInverse.Mat n) (hR:Measurable R) (hC:Measurable C)
    (E V:Ω→State n) (hE:Measurable E) (hV:Measurable V) (second:Bool)
    (choices:List (Fin r×Fin (m+1))) (a:ℝ→ℝ) (ha:Measurable a)
    (F:State d→ℝ) (hF:Measurable F) (mean:Ω→State n) (hm:Measurable mean)
    (g:Fin d→Fin n) (leaf:Fin m→Fin n) (baseline:Ω→Fin m→ℝ)
    (hbase:∀j,Measurable (fun ω=>baseline ω j)):
    Measurable (fun ω=>∫x,TwoFreshFullResidualMoments.word second (A ω) (D ω) (R ω) (C ω)
      (E ω) (V ω) choices a F (fun _:Unit=>mean ω) g leaf (baseline ω) ((),x)
      ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A ω j))).prod
        ((multivariateGaussian (0:State n) (R ω)).prod (multivariateGaussian (0:State n) (C ω)))):=by
  have hold(j:Fin r):Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>
      secondScore (A z.1 j) (D z.1 j) (z.2.1 j)):=by
    have hy:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>z.2.1 j):=
      (measurable_pi_apply j).comp measurable_snd.fst
    have hp:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>((A z.1 j,D z.1 j),z.2.1 j)):=
      (((hA j).comp measurable_fst).prodMk ((hD j).comp measurable_fst)).prodMk hy
    convert! secondScore_measurable.comp hp using 1
  have hnative:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>firstScore (R z.1) (E z.1) z.2.2.1):=by
    convert! firstScore_measurable.comp
      (((hR.comp measurable_fst).prodMk (hE.comp measurable_fst)).prodMk measurable_snd.snd.fst) using 1
  have hfresh:Measurable (fun z:Ω×((Fin r→State n)×(State n×State n))=>factor second (C z.1) (V z.1) z.2.2.2):=by
    cases second
    · convert! firstScore_measurable.comp
        (((hC.comp measurable_fst).prodMk (hV.comp measurable_fst)).prodMk measurable_snd.snd.snd) using 1
    · convert! secondScore_measurable.comp
        (((hC.comp measurable_fst).prodMk (hV.comp measurable_fst)).prodMk measurable_snd.snd.snd) using 1
  have hcp:Measurable (TwoFreshFullResidualMoments.collapse (Ω:=Ω) (r:=r) (n:=n)):=by
    unfold TwoFreshFullResidualMoments.collapse
    fun_prop
  have hroot:=(ParametricAssignedMoments.root_measurable choices 0 F hF mean hm g).comp hcp
  have hleaves:=Finset.measurable_prod Finset.univ
    (fun j _=>(VaryingAssignedFields.leaf_measurable choices j.succ a ha mean hm (leaf j)
      (fun ω=>baseline ω j) (hbase j)).comp hcp)
  apply average_measurable A hA R C hR hC
    (fun z=>TwoFreshFullResidualMoments.word second (A z.1) (D z.1) (R z.1) (C z.1)
      (E z.1) (V z.1) choices a F (fun _:Unit=>mean z.1) g leaf (baseline z.1) ((),z.2))
  convert! ((((Finset.measurable_prod Finset.univ (fun j _=>hold j)).mul hnative).mul hfresh).mul hroot).mul hleaves using 1

end SHE.TwoFreshGaussianFields
