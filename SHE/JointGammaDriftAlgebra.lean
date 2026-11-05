module
public import SHE.FiniteAffineDriftCancellation
public import SHE.JointGammaTestFields
public import SHE.JointPhysicalInsertion
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.JointGammaDriftAlgebra
open GaussianIncrement GaussianTaylor GaussianTaylorAverage GaussianConvolution SmoothCylinders
open FiniteCovariancePullback MeasureTheory
open scoped NNReal
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}{C:Type*}[NormedAddCommGroup C][InnerProductSpace ℝ C]

/-- The literal joint observation is constant on the extended martingale.
Reference covariance cancels exactly, leaving only its true bracket defect. -/
theorem cancellation (P:CanonicalCovariance.ProfileParameters) (Λ θ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
    (Z:Fin n→WordRecursion.Observation) (htarget:∀ i,(b:ℝ)≤(Z i).target)
    {F:State n→ℝ}(hF:BoundedSmooth F) (p:ControlledProfile.Inputs) (t:ℝ)
    (R:Fin ((n+n)+(n+n))→C) (z:FirstGammaAffine.Space n)
    (href:gram (mappedRow (FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)) R)=
      CovarianceMatrix.densityMatrix
        (ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p).coefficient
        Z t):
    JointGammaTestFields.derivative P Λ θ v b hvb Z htarget F p t z+
      (1/2:ℝ)*covarianceAction (gram R)
        (hessian (JointGammaTestFields.value P Λ θ v b hvb Z htarget F p t) z)=
    (1/2:ℝ)*covarianceAction
      (gram (mappedRow (JointGammaAffine.current n Λ θ (fun i=>(Z i).target)) R)-
        CovarianceMatrix.densityMatrix
          (ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p).coefficient Z t)
      (hessian (gaussianAverage
        ((ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p).path t).val F)
        (JointGammaAffine.current n Λ θ (fun i=>(Z i).target) z)):=by
  let W:=ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p
  let L:=JointGammaAffine.current n Λ θ (fun i=>(Z i).target)
  let M:=FirstGammaAffine.reference n Λ θ (fun i=>(Z i).target)
  have hs:BoundedSmooth (gaussianAverage (W.path t).val F):=
    hF.average (ProbabilityTheory.multivariateGaussian (0:State n) (W.path t).val)
  have hh:=FiniteAffineDriftCancellation.cancellation
    (CovarianceMatrix.densityMatrix W.coefficient Z t) L M 0 R hs z href
  have he:JointGammaTestFields.value P Λ θ v b hvb Z htarget F p t=
      (fun w=>gaussianAverage (W.path t).val F (L w)-gaussianAverage (W.path t).val F (M w)):=by
    funext w
    exact JointGammaTestFields.value_apply P Λ θ v b hvb Z htarget F p t w
  rw [he]
  simpa only [JointGammaTestFields.derivative,GaussianEndpointAffine.derivative,
    GaussianAffineFields.mean,add_zero,ContinuousLinearMap.zero_apply,map_zero,add_zero,
    sub_zero,zero_add,L,M,W,ControlledReferenceWindows.window] using hh

/-- The surviving joint bracket is exactly the original local insertion
plus the full cross/quadratic common-Haar defect. -/
theorem insertion_defect (W:CovarianceEndpoint.EndpointWindow n)
    (a:ℝ→ℝ)(ha:Measurable a)(X:ℝ×StoppedFourier.HeatCircle→ℝ)(hX:Measurable X)
    {A:ℝ}(hA:0≤A)(haBound:∀ z,|a z|≤A)(F:State n→ℝ)
    {t:ℝ}(ht:t∈Set.Ioo W.left W.right)(z:State n)
    (G E:Matrix (Fin n) (Fin n) ℝ)
    (hG:G=CovarianceMatrix.densityMatrix (fun p=>a (X p)) W.observations t+E):
    (1/2:ℝ)*covarianceAction (G-CovarianceMatrix.densityMatrix W.coefficient W.observations t)
      (hessian (GaussianItoTest.backward W F t) z)=
      (∫ x:StoppedFourier.HeatCircle,WordRecursion.insertion a W.coefficient W.observations t x
        (GaussianItoTest.backward W F t) (JointPhysicalInsertion.appendState (X (t,x)) z)
        ∂AddCircle.haarAddCircle)+
      (1/2:ℝ)*covarianceAction E (hessian (GaussianItoTest.backward W F t) z):=by
  have hh:=JointPhysicalInsertion.insertion_and_defect W a ha X hX hA haBound F ht z E
  rw [hG,FiniteAffineDriftCancellation.action_sub]
  change -(1/2:ℝ)*covarianceAction (CovarianceMatrix.densityMatrix W.coefficient W.observations t)
      (hessian (GaussianItoTest.backward W F t) z)+
    (1/2:ℝ)*covarianceAction (CovarianceMatrix.densityMatrix (fun p=>a (X p)) W.observations t+E)
      (hessian (GaussianItoTest.backward W F t) z)=_ at hh
  linear_combination hh

end SHE.JointGammaDriftAlgebra
