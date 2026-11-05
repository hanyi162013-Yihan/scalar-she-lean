module

public import SHE.GaussianFractionMixedMoments
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.GaussianFreshFraction
open MeasureTheory ProbabilityTheory GaussianIncrement
open scoped BigOperators
variable {n r : ℕ}

def covariances (T : Matrix (Fin n) (Fin n) ℝ) (A : Fin r→Matrix (Fin n) (Fin n) ℝ) :
    Fin (r+1)→Matrix (Fin n) (Fin n) ℝ := Fin.cases T A

def merge : (State n×(Fin r→State n))×State n→(Fin (r+1)→State n)×State n :=
  fun x => (Fin.cons x.1.1 x.1.2,x.2)

/-- A fresh terminal Gaussian and all original old fractions are
literally the extended finite Gaussian product, with residual untouched. -/
theorem merge_measurePreserving (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ) :
    MeasurePreserving (merge (n:=n) (r:=r))
      (((multivariateGaussian (0:State n) T).prod
        (Measure.pi (fun j => multivariateGaussian (0:State n) (A j)))).prod
        (multivariateGaussian (0:State n) B))
      ((Measure.pi (fun j => multivariateGaussian (0:State n) (covariances T A j))).prod
        (multivariateGaussian (0:State n) B)) := by
  let μ := fun j : Fin (r+1) => multivariateGaussian (0:State n) (covariances T A j)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r+1) => State n) 0).symm
  have he : MeasurePreserving e ((μ 0).prod (Measure.pi (fun j => μ ((0:Fin (r+1)).succAbove j))))
      (Measure.pi μ) := (measurePreserving_piFinSuccAbove μ 0).symm
  have hp := he.prod (MeasurePreserving.id (multivariateGaussian (0:State n) B))
  convert! hp using 1
  funext x
  change (Fin.cons x.1.1 x.1.2,x.2)=((Fin.insertNth 0 x.1.1 x.1.2 : Fin (r+1)→State n),x.2)
  rw [Fin.insertNth_zero']

/-- Genuine Gaussian Fubini for the fresh/old/residual representation.
Integrability is supplied by the proved full-word moment, rather than a
new independence or bounded-kernel assumption. -/
theorem integral_merge (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (F : ((Fin (r+1)→State n)×State n)→ℝ)
    (hF : Integrable F ((Measure.pi (fun j => multivariateGaussian (0:State n) (covariances T A j))).prod
      (multivariateGaussian (0:State n) B))) :
    (∫ z,F z ∂(Measure.pi (fun j => multivariateGaussian (0:State n) (covariances T A j))).prod
      (multivariateGaussian (0:State n) B))=
      ∫ terminal,∫ old,∫ residual,F (Fin.cons terminal old,residual)
        ∂multivariateGaussian 0 B
        ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j))
        ∂multivariateGaussian 0 T := by
  have hm := merge_measurePreserving T A B
  have hi := hm.integrable_comp_of_integrable hF
  have he := hm.hasLaw.integral_comp (f:=F) hF.aestronglyMeasurable
  rw [←he]
  rw [integral_prod _ hi]
  convert! integral_prod _ hi.integral_prod_left using 1

/-- The order used by the literal terminal representation: terminal,
combined residual, then all old fractions. The swap is genuine Fubini
under the already proved full-word integrability. -/
theorem integral_merge_terminal_residual_old (T : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin r→Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (F : ((Fin (r+1)→State n)×State n)→ℝ)
    (hF : Integrable F ((Measure.pi (fun j => multivariateGaussian (0:State n) (covariances T A j))).prod
      (multivariateGaussian (0:State n) B))) :
    (∫ z,F z ∂(Measure.pi (fun j => multivariateGaussian (0:State n) (covariances T A j))).prod
      (multivariateGaussian (0:State n) B))=
      ∫ terminal,∫ residual,∫ old,F (Fin.cons terminal old,residual)
        ∂Measure.pi (fun j => multivariateGaussian (0:State n) (A j))
        ∂multivariateGaussian 0 B ∂multivariateGaussian 0 T := by
  rw [integral_merge T A B F hF]
  have hi := (merge_measurePreserving T A B).integrable_comp_of_integrable hF
  have hp := (measurePreserving_prodAssoc (multivariateGaussian (0:State n) T)
    (Measure.pi (fun j => multivariateGaussian (0:State n) (A j))) (multivariateGaussian (0:State n) B)).symm
  have hassoc := hp.integrable_comp_of_integrable hi
  apply integral_congr_ae
  filter_upwards [hassoc.prod_right_ae] with terminal ht
  have ht' : Integrable
      (Function.uncurry (fun (old : Fin r→State n) (residual : State n) =>
        F (Fin.cons terminal old,residual)))
      ((Measure.pi (fun j => multivariateGaussian (0:State n) (A j))).prod
        (multivariateGaussian (0:State n) B)) := by
    convert! ht using 1
  convert! integral_integral_swap ht' using 1

end SHE.GaussianFreshFraction
