module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import SHE.HilbertBandTails
public import SHE.HilbertDyadicConvergence

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.HilbertFiniteRateTails
open Classical Set Filter MeasureTheory Real PredictableL2
open scoped BigOperators ENNReal

/-- A genuine Banach-space band with finitely many energy mechanisms
retains each separate tail exponent; no bad-tail rate is replaced by
the slow current exponent. -/
theorem vector {ι V:Type*}[Fintype ι][NormedAddCommGroup V][CompleteSpace V]
    (γ A:ι→ℝ)(hγ:∀i,0<γ i)(hA:∀i,0≤A i){R:ℝ}(hR:0<R)
    (v:ℕ→V)(hv:∀n,‖v n‖≤∑i,A i*(R*(2:ℝ)^n)^(-γ i)):
    Summable v ∧ ‖∑'n,v n‖≤∑i,A i*StateBands.geometricConstant (γ i)*R^(-γ i):=by
  have hs(i:ι):Summable (fun n:ℕ=>A i*(R*(2:ℝ)^n)^(-γ i)):=
    (StateBands.geometric_bands (hγ i) hR).1.mul_left (A i)
  have hm:Summable (fun n:ℕ=>∑i,A i*(R*(2:ℝ)^n)^(-γ i)):=
    summable_sum (fun i _=>hs i)
  refine ⟨Summable.of_norm_bounded hm hv,?_⟩
  calc
    _≤∑'n,∑i,A i*(R*(2:ℝ)^n)^(-γ i):=tsum_of_norm_bounded hm.hasSum hv
    _=∑i,A i*StateBands.geometricConstant (γ i)*R^(-γ i):=by
      rw [Summable.tsum_finsetSum (fun i _=>hs i)]
      apply Finset.sum_congr rfl
      intro i _
      rw [tsum_mul_left,(StateBands.geometric_bands (hγ i) hR).2]
      ring

variable {X E:Type*}[MeasurableSpace X][NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (μ:Measure X)(F:ℕ→X→E)(hF:∀j,Measurable (F j))
variable (hi:∀j,Integrable (fun x=>‖F j x‖^2) μ)
local notation "V"=>HilbertBandTails.vector μ F hF hi

/-- The four native mechanisms may be correlated inside each actual
field. Their actual product-L2 bands nevertheless sum strongly, with
the separate current/past/good/bad geometric cutoff tails. -/
theorem dyadic {ι:Type*}[Fintype ι](γ A:ι→ℝ)(hγ:∀i,0<γ i)(hA:∀i,0≤A i)
    (hb:∀j,(∫x,‖F j x‖^2 ∂μ)≤∑i,(A i)^2*((2:ℝ)^j)^(-2*γ i)):
    Summable V ∧ ∀J:ℕ,‖∑'n,V (n+J)‖≤
      ∑i,A i*StateBands.geometricConstant (γ i)*((2:ℝ)^J)^(-γ i):=by
  have hv(j:ℕ):‖V j‖≤∑i,A i*((2:ℝ)^j)^(-γ i):=by
    have hh:=hb j
    rw [←HilbertBandTails.vector_norm_sq μ F hF hi j] at hh
    have he:(∑i,(A i)^2*((2:ℝ)^j)^(-2*γ i))=
        ∑i,(A i*((2:ℝ)^j)^(-γ i))^2:=by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow,←rpow_mul_natCast (show 0≤(2:ℝ)^j by positivity)]
      congr 2
      ring
    rw [he] at hh
    have hpos(i:ι):0≤A i*((2:ℝ)^j)^(-γ i):=mul_nonneg (hA i) (rpow_nonneg (by positivity) _)
    have hs:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (fun i _=>hpos i)
    have hsum:0≤∑i,A i*((2:ℝ)^j)^(-γ i):=Finset.sum_nonneg (fun i _=>hpos i)
    nlinarith [norm_nonneg (V j)]
  have hs:=vector γ A hγ hA (by norm_num:(0:ℝ)<1) V
    (fun j=>by simpa only [one_mul] using hv j)
  refine ⟨hs.1,fun J=>?_⟩
  exact (vector γ A hγ hA (by positivity:(0:ℝ)<(2:ℝ)^J) (fun n=>V (n+J))
    (fun n=>by simpa only [pow_add,mul_comm ((2:ℝ)^n)] using hv (n+J))).2

end SHE.HilbertFiniteRateTails
