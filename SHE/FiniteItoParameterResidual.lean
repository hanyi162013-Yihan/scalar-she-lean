module

public import SHE.StandardFiniteIto
public import SHE.PastParameterItoIdentity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.FiniteItoParameterResidual
open Set MeasureTheory PredictableL2 GaussianItoTest GaussianTaylorAverage Filter Topology
open scoped NNReal ENNReal
variable {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
variable {n : ℕ} (Y : ℝ≥0×Ω→WordRecursion.State n)
variable (D : Ω→ℝ→Matrix (Fin n) (Fin n) ℝ)
variable (a b : ℝ) (G dG : X→ℝ→WordRecursion.State n→ℝ)

def drift (x : X) (ω : Ω) (t : ℝ) : ℝ := dG x t (Y (t.toNNReal,ω))+
  (1/2:ℝ)*covarianceAction (D ω t) (GaussianTaylor.hessian (G x t) (Y (t.toNNReal,ω)))

def residual (x : X) (ω : Ω) : ℝ :=
  G x b (Y (b.toNNReal,ω))-G x a (Y (a.toNNReal,ω))-
    ∫ t in a..b,drift Y D G dG x ω t

/-- Joint continuity of the actual test, its time derivative and Hessian,
with one genuine integrable drift envelope, gives pathwise continuity
of the entire finite-Itô residual in the frozen past parameter. -/
theorem continuous_residual (hab : a≤b)
    (hG : Continuous (fun p : X×(ℝ×WordRecursion.State n)=>G p.1 p.2.1 p.2.2))
    (hH : Continuous (fun p : X×(ℝ×WordRecursion.State n)=>GaussianTaylor.hessian (G p.1 p.2.1) p.2.2))
    (hdG : ∀ t,Continuous (fun p : X×WordRecursion.State n=>dG p.1 t p.2))
    (ω : Ω) (m : ℝ→ℝ) (hm : IntervalIntegrable m volume a b)
    (hmeas : ∀ x,AEStronglyMeasurable (drift Y D G dG x ω) (volume.restrict (Ioc a b)))
    (hbound : ∀ x,∀ᵐ t∂volume.restrict (Ioc a b),‖drift Y D G dG x ω t‖≤m t) :
    Continuous (fun x=>residual Y D a b G dG x ω) := by
  have hint : Continuous (fun x=>∫ t,drift Y D G dG x ω t ∂volume.restrict (Ioc a b)) := by
    apply continuous_of_dominated (bound:=m) hmeas hbound hm.1
    exact ae_of_all _ (fun t=>by
      have hess := hH.comp (continuous_id.prodMk (continuous_const (y:=(t,Y (t.toNNReal,ω)))))
      have htime := (hdG t).comp (continuous_id.prodMk (continuous_const (y:=Y (t.toNNReal,ω))))
      apply htime.add
      apply Continuous.const_mul
      unfold covarianceAction
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul ((hess.clm_apply continuous_const).clm_apply continuous_const))
  have hga := hG.comp (continuous_id.prodMk (continuous_const (y:=(a,Y (a.toNNReal,ω)))))
  have hgb := hG.comp (continuous_id.prodMk (continuous_const (y:=(b,Y (b.toNNReal,ω)))))
  convert (hgb.sub hga).sub hint using 1
  funext x
  exact congrArg (fun q=>G x b (Y (b.toNNReal,ω))-G x a (Y (a.toNNReal,ω))-q)
    (intervalIntegral.integral_of_le hab)

end SHE.FiniteItoParameterResidual
