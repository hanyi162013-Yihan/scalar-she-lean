module
public import SHE.BrownianFiniteCovariance
public import SHE.GaussianDifferenceMap
public import SHE.StandardTerminalLevy
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.BrownianShiftedFiniteLaw
open MeasureTheory ProbabilityTheory WordRecursion Set
open scoped NNReal
variable{Ω ι:Type*}[MeasurableSpace Ω][DecidableEq ι]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(X:ι→ℝ≥0→Ω→ℝ)
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))
include hBrown

/-- The actual future Brownian finite laws have the RELATIVE time
covariance after subtracting the original restart value. -/
theorem law(v h:ℝ≥0)(hvh:v+h≤H){n:ℕ}(a:Fin n→ι)(t:Fin n→ℝ≥0)(ht:∀i,t i≤h):
    HasLaw (fun ω=>WithLp.toLp 2 (fun i=>X (a i) (v+t i) ω-X (a i) v ω))
      (multivariateGaussian (0:State n) (BrownianFiniteCovariance.matrix a t)) μ:=by
  let aa:Fin (n+n)→ι:=Fin.addCases a a
  let tt:Fin (n+n)→ℝ≥0:=Fin.addCases (fun i=>v+t i) (fun _=>v)
  have htt:∀i,tt i≤H:=Fin.addCases
    (fun i=>by
      simpa only[tt,Fin.addCases_left] using (add_le_add_right (ht i) v).trans hvh)
    (fun i=>by
      simpa only[tt,Fin.addCases_right] using
        (show v≤v+h from le_add_of_nonneg_right (by positivity)).trans hvh)
  have hl:HasLaw (fun ω=>WithLp.toLp 2 (fun i=>X (aa i) (tt i) ω))
      (multivariateGaussian (0:State (n+n)) (BrownianFiniteCovariance.matrix aa tt)) μ:=
    (hBrown (n+n) aa).1 tt htt
  have he:∀i j,BrownianFiniteCovariance.matrix a t i j=
      BrownianFiniteCovariance.matrix aa tt (Fin.castAdd n i) (Fin.castAdd n j)-
      BrownianFiniteCovariance.matrix aa tt (Fin.castAdd n i) (Fin.natAdd n j)-
      BrownianFiniteCovariance.matrix aa tt (Fin.natAdd n i) (Fin.castAdd n j)+
      BrownianFiniteCovariance.matrix aa tt (Fin.natAdd n i) (Fin.natAdd n j):=by
    intro i j
    have h1:min (v+t i) (v+t j)=v+min (t i) (t j):=min_add_add_left _ _ _
    have h2:min (v+t i) v=v:=min_eq_right (le_add_of_nonneg_right (by positivity))
    have h3:min v (v+t j)=v:=min_eq_left (le_add_of_nonneg_right (by positivity))
    simp only[BrownianFiniteCovariance.matrix,aa,tt,Fin.addCases_left,Fin.addCases_right,h1,h2,h3,min_self]
    push_cast
    ring
  have hd:HasLaw (GaussianDifferenceMap.difference (Fin.castAdd n) (Fin.natAdd n))
      (multivariateGaussian (0:State n) (BrownianFiniteCovariance.matrix a t))
      (multivariateGaussian (0:State (n+n)) (BrownianFiniteCovariance.matrix aa tt)):=
    ⟨(GaussianDifferenceMap.difference _ _).measurable.aemeasurable,
      GaussianDifferenceMap.map _ _ (BrownianFiniteCovariance.posSemidef aa tt)
        (BrownianFiniteCovariance.posSemidef a t) he⟩
  have hfun:(GaussianDifferenceMap.difference (Fin.castAdd n) (Fin.natAdd n)) ∘
      (fun ω=>WithLp.toLp 2 (fun i=>X (aa i) (tt i) ω))=
      (fun ω=>WithLp.toLp 2 (fun i=>X (a i) (v+t i) ω-X (a i) v ω)):=by
    funext ω
    apply PiLp.ext
    intro i
    change X (aa (Fin.castAdd n i)) (tt (Fin.castAdd n i)) ω-
      X (aa (Fin.natAdd n i)) (tt (Fin.natAdd n i)) ω= _
    simp only[aa,tt,Fin.addCases_left,Fin.addCases_right]
  have hh:=hd.comp hl
  rwa[hfun] at hh
end SHE.BrownianShiftedFiniteLaw
