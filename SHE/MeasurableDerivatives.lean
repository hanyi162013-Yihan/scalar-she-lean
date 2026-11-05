module

public import SHE.ObservationMeasurable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Joint Borel derivatives for arbitrary measurable parameter spaces.
The parameter need not carry a topology or have continuous dependence. -/
noncomputable section
namespace SHE.MeasurableDerivatives
open Set MeasureTheory Filter StoppedFourier

abbrev State (n : ℕ) := WordRecursion.State n
variable {P : Type*} [MeasurableSpace P]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G]

theorem directional_measurable {n : ℕ} {F : P → State n → G}
    (hF : Measurable (fun p : P × State n => F p.1 p.2))
    (hd : ∀ p, Differentiable ℝ (F p)) (v : State n) :
    Measurable (fun p : P × State n => fderiv ℝ (F p.1) p.2 v) := by
  have hc : Tendsto (fun k : ℕ => ‖(k : ℝ)‖) atTop atTop := by
    simpa only [Real.norm_natCast] using (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
  apply measurable_of_tendsto_metrizable (f := fun k p => (k : ℝ) •
    (F p.1 (p.2 + (k : ℝ)⁻¹ • v) - F p.1 p.2))
  · intro k
    have hmap : Measurable (fun p : P × State n => (p.1, p.2 + (k : ℝ)⁻¹ • v)) := by fun_prop
    exact ((hF.comp hmap).sub hF).const_smul _
  · apply tendsto_pi_nhds.mpr
    intro p
    exact (hd p.1 p.2).hasFDerivAt.lim v hc

theorem fderiv_measurable {n : ℕ} {F : P → State n → G}
    (hF : Measurable (fun p : P × State n => F p.1 p.2))
    (hd : ∀ p, Differentiable ℝ (F p)) :
    Measurable (fun p : P × State n => fderiv ℝ (F p.1) p.2) := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hcols (i : Fin n) := directional_measurable hF hd (e i)
  have hs : Measurable (fun p : P × State n => ∑ i : Fin n,
      (ContinuousLinearMap.smulRightL ℝ (State n) G (EuclideanSpace.proj i)) (fderiv ℝ (F p.1) p.2 (e i))) := by
    apply Finset.measurable_sum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (State n) G (EuclideanSpace.proj i)).measurable.comp (hcols i)
  convert hs using 1
  funext p
  ext z
  have hz : (∑ i : Fin n, z i • e i) = z := by
    simpa only [e, EuclideanSpace.basisFun_repr] using e.sum_repr z
  calc
    _ = (fderiv ℝ (F p.1) p.2) (∑ i : Fin n, z i • e i) := by rw [hz]
    _ = ∑ i : Fin n, z i • fderiv ℝ (F p.1) p.2 (e i) := by simp only [map_sum, map_smul]
    _ = _ := by simp

theorem hessian_measurable {n : ℕ} {F : P → State n → ℝ}
    (hF : Measurable (fun p : P × State n => F p.1 p.2))
    (hC : ∀ p, ContDiff ℝ 2 (F p)) :
    Measurable (fun p : P × State n => GaussianTaylor.hessian (F p.1) p.2) := by
  exact fderiv_measurable (fderiv_measurable hF (fun p => (hC p).differentiable (by norm_num)))
    (fun p => ((hC p).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num))

end SHE.MeasurableDerivatives
