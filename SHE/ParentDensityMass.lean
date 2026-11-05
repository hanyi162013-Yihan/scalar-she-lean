module

public import SHE.ParentMeanMass
public import SHE.NativeHeatKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ParentMeanDensity
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain
open scoped BigOperators
local instance parentDensityMass_period : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- A terminal square-root heat sum has finite spatial L2 mass with a
pure dimension constant. No lower bound on individual target ages is paid. -/
theorem sqrt_heat_sum_square_mass {n : ℕ} (t : Fin n→ℝ) (x : Fin n→HeatCircle)
    (ht : ∀ i,0<t i) :
    Integrable (fun y=>(∑ i : Fin n,sqrt ‖ProfileVariance.heatPhysical (t i) (x i) y‖)^2) haarAddCircle ∧
      (∫ y,(∑ i : Fin n,sqrt ‖ProfileVariance.heatPhysical (t i) (x i) y‖)^2 ∂haarAddCircle)≤(n:ℝ)^2 := by
  have hc (i : Fin n) : Continuous (fun y=>‖ProfileVariance.heatPhysical (t i) (x i) y‖):=
    ((NativeHeatSpan.continuous_heatPhysical_space (ht i)).comp (continuous_const.prodMk continuous_id)).norm
  have hi (i : Fin n) : Integrable (fun y=>‖ProfileVariance.heatPhysical (t i) (x i) y‖) haarAddCircle:=
    (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass (i : Fin n) : (∫ y,‖ProfileVariance.heatPhysical (t i) (x i) y‖ ∂haarAddCircle)=1:=by
    simpa only [NativeHeatSpan.kernel_eq_physical] using NativeHeatSpan.kernel_norm_mass (ht i) (x i)
  have hsum : Integrable (fun y=>(∑ i : Fin n,sqrt ‖ProfileVariance.heatPhysical (t i) (x i) y‖)^2) haarAddCircle:=
    ((continuous_finset_sum _ (fun i _=>Real.continuous_sqrt.comp (hc i))).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  refine ⟨hsum,?_⟩
  have hb (y : HeatCircle) : (∑ i : Fin n,sqrt ‖ProfileVariance.heatPhysical (t i) (x i) y‖)^2≤
      (n:ℝ)*∑ i : Fin n,‖ProfileVariance.heatPhysical (t i) (x i) y‖ := by
    simpa only [one_mul,one_pow,Real.sq_sqrt (norm_nonneg _),Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n=>(1:ℝ))
        (fun i=>sqrt ‖ProfileVariance.heatPhysical (t i) (x i) y‖)
  have hh:=integral_mono hsum ((integrable_finsetSum Finset.univ (fun i _=>hi i)).const_mul (n:ℝ)) hb
  rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)] at hh
  simpa only [hmass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,pow_two] using hh

variable {X : Type} [MeasurableSpace X] {R : ReferenceData} (L : Level R X 1)

theorem globalDensity_square_mass (k : ℕ) (p : History X k) {r : ℝ}
    (hr : r<(carrier L k).terminal p) :
    Integrable (fun y=>globalDensity L k p r y^2) haarAddCircle ∧
      (∫ y,globalDensity L k p r y^2 ∂haarAddCircle)≤
        ((1+k:ℕ):ℝ)^2*parentProduct L k p^2 := by
  have he : (fun y=>globalDensity L k p r y^2)=fun y=>parentProduct L k p^2*
      (∑ i : Fin (1+k),sqrt ‖ProfileVariance.heatPhysical
        (4*(((carrier L k).observations.observations p i).target-r))
        ((carrier L k).observations.observations p i).center y‖)^2 := by
    funext y
    exact mul_pow _ _ 2
  have hj:=sqrt_heat_sum_square_mass (fun i=>4*(((carrier L k).observations.observations p i).target-r))
    (fun i=>((carrier L k).observations.observations p i).center)
    (fun i=>mul_pos (by norm_num) (sub_pos.mpr (hr.trans_le ((carrier L k).targets_after p i))))
  rw [he]
  refine ⟨hj.1.const_mul _,?_⟩
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hj.2 (sq_nonneg _)).trans_eq (mul_comm _ _)

end SHE.ParentMeanDensity
