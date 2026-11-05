module

public import SHE.ScalarBandBernstein
public import SHE.ScalarRootLevel
public import SHE.RootSmoothSums

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ScalarRootBands
open Set Filter Real MeasureTheory ScalarDyadicBands ScalarBandBernstein
  SmoothCylinders UniformSmooth WordRecursion
open scoped ContDiff Topology
variable {X : Type} [MeasurableSpace X]

def test (a : ℝ→ℝ) (ψ : X→ℝ) (j : ℕ) (x : X) (z : State 1) : ℝ :=
  ψ x*band a j (z 0)

theorem test_uniform {a : ℝ→ℝ} (ha : Continuous a) {B : ℝ} (hB : ∀ x,|a x|≤B)
    (ψ : X→ℝ) {W : ℝ} (hW : 0≤W) (hψ : ∀ x,|ψ x|≤W) (j : ℕ) :
    UniformBoundedSmooth (test a ψ j) := by
  have hp : UniformBoundedSmooth (fun x (_ : State 1)=>ψ x):=
    UniformBoundedSmooth.parameter_const ψ hW (fun x=>by simpa only [Real.norm_eq_abs] using hψ x)
  have ha' : UniformBoundedSmooth (fun _ : X=>band a j):=
    UniformBoundedSmooth.fixed (band_boundedSmooth ha hB j)
  exact hp.mul (ha'.comp_right (EuclideanSpace.proj (0:Fin 1)))

theorem test_measurable {a : ℝ→ℝ} (ha : Continuous a) {B : ℝ} (hB : ∀ x,|a x|≤B)
    (ψ : X→ℝ) (hψ : Measurable ψ) (j : ℕ) :
    Measurable (fun z : X×State 1=>test a ψ j z.1 z.2) :=
  (hψ.comp measurable_fst).mul ((band_boundedSmooth ha hB j).smooth.continuous.measurable.comp
    ((EuclideanSpace.proj (0:Fin 1)).continuous.measurable.comp measurable_snd))

/-- These are exactly the finite-order root jet hypotheses used by the
actual stochastic band estimates, for a CONSTRUCTED bounded scalar
Holder root. No unspecified band family remains in this input. -/
theorem test_jets {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (ψ : X→ℝ) {W : ℝ}
    (hW : 0≤W) (hψ : ∀ x,|ψ x|≤W) (k j : ℕ) (x : X) (l : ℕ) (hl : l≤k) (z : State 1) :
    ‖iteratedFDeriv ℝ l (test a ψ j x) z‖≤
      ((W*amplitude B H k)*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^l := by
  let L : State 1→L[ℝ] ℝ:=EuclideanSpace.proj (0:Fin 1)
  have hL : ‖L‖≤1 := L.opNorm_le_bound zero_le_one (fun y=>by
    change ‖y (0:Fin 1)‖≤1*‖y‖
    simpa only [one_mul] using (PiLp.norm_apply_le y (0:Fin 1)))
  have hA:=amplitude_nonneg (B:=B) hH k
  have hs := (band_boundedSmooth ha hB j).smooth
  have hc : ‖iteratedFDeriv ℝ l (band a j ∘ L) z‖≤
      (amplitude B H k*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^l := by
    rw [L.iteratedFDeriv_comp_right hs z (by simp)]
    have hn := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ l (band a j) (L z)) (fun _=>L)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
    have hp : ‖L‖^l≤1:=by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL l
    exact hn.trans ((mul_le_mul (all_jets ha hB hH hβ hβ1 hh k j l hl (L z)) hp
      (pow_nonneg (norm_nonneg L) l) (by positivity : 0≤(amplitude B H k*((2:ℝ)^j)^(-β))*((2:ℝ)^j)^l)).trans_eq (mul_one _))
  change ‖iteratedFDeriv ℝ l (fun y=>ψ x • (band a j ∘ L) y) z‖≤_
  rw [iteratedFDeriv_const_smul_apply' ((hs.comp L.contDiff).of_le (by simp)).contDiffAt,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul (hψ x) hc (norm_nonneg _) hW).trans_eq (by ring)

theorem rootSum_eq (a : ℝ→ℝ) (ψ : X→ℝ) (J : ℕ) (x : X) (z : State 1) :
    RootSmoothSums.rootSum (test a ψ) (Finset.range (J+1)) x z=ψ x*smooth a J (z 0) := by
  simp only [RootSmoothSums.rootSum,test,←Finset.mul_sum,sum_band]

theorem cutoff_error {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (ψ : X→ℝ) {W : ℝ}
    (hW : 0≤W) (hψ : ∀ x,|ψ x|≤W) (J : ℕ) (x : X) (z : State 1) :
    |RootSmoothSums.rootSum (test a ψ) (Finset.range (J+1)) x z-ψ x*a (z 0)|≤
      W*H*CompactMollifier.radius J^β := by
  rw [rootSum_eq,←mul_sub,abs_mul]
  exact (mul_le_mul (hψ x) (smooth_error ha hB hH hβ hh J (z 0)) (abs_nonneg _) hW).trans_eq (by ring)

end SHE.ScalarRootBands
