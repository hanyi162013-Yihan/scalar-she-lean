module
public import SHE.ScalarThetaMinkowski
public import SHE.FiniteForestLeafInput
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.ScalarFiniteThetaResidual
open Set MeasureTheory ProfileL2
open scoped BigOperators
variable {Θ Ω ι:Type*}[MeasurableSpace Θ][MeasurableSpace Ω][Fintype ι]

/-- Interpolation averaging and the finite signed baseline sum commute
on the real sample event. Correlated terms enter through the L2 triangle
inequality; no independence or pointwise sample bound is required. -/
theorem bound (μ:Measure Ω)[SFinite μ](τ:Measure Θ)[SFinite τ]
    (C:Θ×Ω→ℝ)(B:ι→Θ×Ω→ℝ)
    (hCi:Integrable C (τ.prod μ))(hBi:∀j,Integrable (B j) (τ.prod μ))
    (hC:MemLp (fun ω=>∫θ,C (θ,ω) ∂τ) 2 μ)
    (hB:∀j,MemLp (fun ω=>∫θ,B j (θ,ω) ∂τ) 2 μ)
    (a:ℝ)(b:ι→ℝ)
    (hCa:normTwo μ (fun ω=>∫θ,C (θ,ω) ∂τ)≤a)
    (hBb:∀j,normTwo μ (fun ω=>∫θ,B j (θ,ω) ∂τ)≤b j):
    Integrable (fun z=>C z-∑j,B j z) (τ.prod μ) ∧
    MemLp (fun ω=>∫θ,(C (θ,ω)-∑j,B j (θ,ω)) ∂τ) 2 μ ∧
    normTwo μ (fun ω=>∫θ,(C (θ,ω)-∑j,B j (θ,ω)) ∂τ)≤a+∑j,b j:=by
  classical
  let c:=fun ω=>∫θ,C (θ,ω) ∂τ
  let d:=fun ω=>∑j,∫θ,B j (θ,ω) ∂τ
  have hdi:Integrable (fun z=>∑j,B j z) (τ.prod μ):=
    integrable_finset_sum Finset.univ (fun j _=>hBi j)
  have hd:MemLp d 2 μ:=memLp_finsetSum Finset.univ (fun j _=>hB j)
  have he: (fun ω=>∫θ,(C (θ,ω)-∑j,B j (θ,ω)) ∂τ)=ᵐ[μ](fun ω=>c ω-d ω):=by
    filter_upwards [hCi.prod_left_ae,hdi.prod_left_ae,
      ae_all_iff.mpr (fun j=> (hBi j).prod_left_ae)] with ω hc hd hb
    rw [integral_sub hc hd,integral_finset_sum Finset.univ (fun j _=>hb j)]
  have hres:MemLp (fun ω=>∫θ,(C (θ,ω)-∑j,B j (θ,ω)) ∂τ) 2 μ:=
    (memLp_congr_ae he).mpr (hC.sub hd)
  refine ⟨hCi.sub hdi,hres,?_⟩
  rw [normTwo_congr_ae he]
  have hneg:MemLp (fun ω=>(-1:ℝ)*d ω) 2 μ:=hd.const_mul (-1)
  have htriangle:=normTwo_add hC hneg
  have heq:(fun ω=>c ω-d ω)=(c+(fun ω=>(-1:ℝ)*d ω)):=by funext ω;dsimp;ring
  rw [heq]
  refine htriangle.trans ?_
  rw [normTwo_const_mul hd (-1)]
  simp only [abs_neg,abs_one,one_mul]
  have hsum:=FiniteForestLeafInput.normTwo_finset_sum Finset.univ
    (fun j ω=>∫θ,B j (θ,ω) ∂τ) (fun j _=>hB j)
  exact add_le_add hCa (hsum.trans (Finset.sum_le_sum (fun j _=>hBb j)))
end SHE.ScalarFiniteThetaResidual
