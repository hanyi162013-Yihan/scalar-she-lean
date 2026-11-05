module

public import SHEStochastic.KernelMarkovGaussianSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.GaussianPastAddition
open MeasureTheory ProbabilityTheory SHE.GaussianIncrement
variable {Z : Type*} [MeasurableSpace Z] {m : ℕ}

theorem prod_add (ρ : Measure Z) [SFinite ρ] (μ ν : Measure (State m)) [SFinite μ] [SFinite ν] :
    ((ρ.prod μ).prod ν).map (fun z => (z.1.1,z.1.2+z.2))=ρ.prod (μ ∗ ν) := by
  calc
    _ = (((ρ.prod μ).prod ν).map MeasurableEquiv.prodAssoc).map
        (Prod.map id (fun p : State m×State m => p.1+p.2)) := by
      rw [Measure.map_map (measurable_id.prodMap (by fun_prop)) (by fun_prop)]
      rfl
    _ = (ρ.prod (μ.prod ν)).map (Prod.map id (fun p : State m×State m => p.1+p.2)) := by
      rw [Measure.prodAssoc_prod]
    _ = ρ.prod ((μ.prod ν).map (fun p => p.1+p.2)) := by
      rw [←Measure.map_prod_map ρ (μ.prod ν) measurable_id (by fun_prop),Measure.map_id]
    _ = _ := rfl

/-- Adding a new Gaussian increment independent of the full joint
past preserves independence from that past and adds the covariances. -/
theorem law {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (g : Ω → Z) (hg : Measurable g) (x y : Ω → State m) (hx : Measurable x) (hy : Measurable y)
    (A B : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hPast : Q.map (fun ω => (g ω,x ω))=(Q.map g).prod (multivariateGaussian (0 : State m) A))
    (hFresh : Q.map (fun ω => ((g ω,x ω),y ω))=
      (Q.map (fun ω => (g ω,x ω))).prod (multivariateGaussian (0 : State m) B)) :
    Q.map (fun ω => (g ω,x ω+y ω))=(Q.map g).prod (multivariateGaussian (0 : State m) (A+B)) := by
  calc
    _ = (Q.map (fun ω => ((g ω,x ω),y ω))).map (fun z => (z.1.1,z.1.2+z.2)) := by
      rw [Measure.map_map (by fun_prop) ((hg.prodMk hx).prodMk hy)]
      rfl
    _ = (((Q.map g).prod (multivariateGaussian (0 : State m) A)).prod
        (multivariateGaussian (0 : State m) B)).map (fun z => (z.1.1,z.1.2+z.2)) := by rw [hFresh,hPast]
    _ = _ := by rw [prod_add,gaussian_convolution hA hB]

end SHEStochastic.GaussianPastAddition
