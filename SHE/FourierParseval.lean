module

public import SHE.FourierHeatLine
public import SHE.GlobalHeatSpan
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.FourierParseval
open MeasureTheory Finset SHE.HeatLine SHE.FourierCluster SHE.FourierHeatLine
open scoped FourierTransform InnerProductSpace

theorem integrable_heatEntire {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Integrable (fun x : ℝ => heatEntire t a (x:ℂ)) := by
  have hb : 0 < (((1/(4*t):ℝ):ℂ)).re := by simp only [Complex.ofReal_re]; positivity
  have hh := (integrable_cexp_neg_mul_sq hb).comp_sub_right a
  convert hh using 1
  funext x
  unfold heatEntire
  congr 1
  push_cast
  ring

theorem integrable_frequencyGaussian {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Integrable (fun ξ : ℝ => frequencyGaussian t a (ξ:ℂ)) := by
  have hb : 0 < (((4*Real.pi^2*t:ℝ):ℂ)).re := by simp only [Complex.ofReal_re]; positivity
  convert integrable_cexp_quadratic hb (((-2*Real.pi*a:ℝ):ℂ)*Complex.I) 0 using 1
  funext ξ
  simp [frequencyGaussian,SHE.HeatAnnihilator.gaussian,frequencyParameter]

theorem fourier_finite_sum {I : Type*} [Fintype I] (f : I → ℝ → ℂ)
    (hf : ∀ i,Integrable (f i)) :
    𝓕 (fun x : ℝ => ∑ i,f i x) = fun ξ => ∑ i,𝓕 (f i) ξ := by
  funext ξ
  simp only [Real.fourier_real_eq,Finset.smul_sum]
  rw [integral_finsetSum]
  intro i _
  simpa only [Real.inner_apply,mul_comm] using (Real.fourierIntegral_convergent_iff ξ).mpr (hf i)

theorem fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x => c*f x) = fun ξ => c*𝓕 f ξ := by
  funext ξ
  simp only [Real.fourier_real_eq_integral_exp_smul,smul_eq_mul]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul c _

/-- Parseval follows directly from the checked deterministic Fourier
Fubini and inversion theorems, with their true L¹ hypotheses. -/
theorem integral_inner_fourier {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hFg : Integrable (𝓕 g)) (hgc : Continuous g) :
    (∫ ξ : ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ)) = ∫ x : ℝ,inner ℂ (f x) (g x) := by
  have hh := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip (innerSL ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hFg
  rw [flip_innerₗ] at hh
  have hinv := hgc.fourierInv_fourier_eq hg hFg
  change (∫ ξ : ℝ,inner ℂ (𝓕 f ξ) (𝓕 g ξ)) =
    ∫ x : ℝ,inner ℂ (f x) (𝓕⁻ (𝓕 g) x) at hh
  rwa [hinv] at hh

def physicalSum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ) (x : ℝ) : ℂ :=
  ∑ i,z i*heatEntire (t i) (a i) (x:ℂ)

def frequencySum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ) (ξ : ℝ) : ℂ :=
  ∑ i,z i*(heatMass (t i):ℂ)*frequencyGaussian (t i) (a i) (ξ:ℂ)

theorem integrable_physicalSum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) : Integrable (physicalSum t a z) :=
  integrable_finsetSum univ (fun i _ => (integrable_heatEntire (ht i) (a i)).const_mul (z i))

theorem integrable_frequencySum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) : Integrable (frequencySum t a z) :=
  integrable_finsetSum univ (fun i _ => (integrable_frequencyGaussian (ht i) (a i)).const_mul _)

theorem fourier_physicalSum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) : 𝓕 (physicalSum t a z) = frequencySum t a z := by
  unfold physicalSum
  rw [fourier_finite_sum _ (fun i => (integrable_heatEntire (ht i) (a i)).const_mul (z i))]
  funext ξ
  simp only [fourier_const_mul,frequencySum,fourier_heatEntire (ht _) _,mul_assoc]

theorem frequencyGaussian_norm (t a ξ : ℝ) :
    ‖frequencyGaussian t a (ξ:ℂ)‖ = Real.exp (-(4*Real.pi^2*t)*ξ^2) := by
  unfold frequencyGaussian SHE.HeatAnnihilator.gaussian frequencyParameter
  rw [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

theorem memLp_two_of_integrable_bounded (f : ℝ → ℂ) (hf : Integrable f)
    (hb : ∀ x,‖f x‖ ≤ 1) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply hf.norm.mono' (hf.aestronglyMeasurable.norm.pow 2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.pow_apply]
  nlinarith [norm_nonneg (f x),hb x]

theorem memLp_frequencyGaussian {t : ℝ} (ht : 0 < t) (a : ℝ) :
    MemLp (fun ξ : ℝ => frequencyGaussian t a (ξ:ℂ)) 2 volume := by
  apply memLp_two_of_integrable_bounded _ (integrable_frequencyGaussian ht a)
  intro ξ
  rw [frequencyGaussian_norm,Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg ξ)

theorem memLp_frequencySum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) : MemLp (frequencySum t a z) 2 volume :=
  memLp_finsetSum univ (fun i _ => (memLp_frequencyGaussian (ht i) (a i)).const_mul _)

theorem physicalSum_span {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ) :
    (∑ i,z i • heatEntire (t i) (a i)) ∈ Submodule.span ℂ
      (Set.range (fun i => heatEntire (t i) (a i))) :=
  (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨z,rfl⟩

theorem continuous_physicalSum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ) :
    Continuous (physicalSum t a z) := by
  unfold physicalSum
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using
    SHE.HeatCluster.continuous_heat_span t a _ (physicalSum_span t a z)

theorem memLp_physicalSum {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) : MemLp (physicalSum t a z) 2 volume := by
  obtain ⟨C,hC,hb⟩ := SHE.GlobalHeatSpan.global_heat_span_envelope q
  have hi := (hb t a ht _ (physicalSum_span t a z)).1
  apply (memLp_two_iff_integrable_sq_norm (continuous_physicalSum t a z).aestronglyMeasurable).mpr
  simpa only [physicalSum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hi

theorem integral_norm_sq_fourier {f : ℝ → ℂ} (hf : Integrable f) (hF : Integrable (𝓕 f))
    (hc : Continuous f) (hf2 : MemLp f 2 volume) (hF2 : MemLp (𝓕 f) 2 volume) :
    (∫ ξ : ℝ,‖𝓕 f ξ‖^2) = ∫ x : ℝ,‖f x‖^2 := by
  have hh := integral_inner_fourier hf hf hF hc
  rw [← SHE.StoppedFourier.toLp_inner_eq_integral hF2 hF2,
    ← SHE.StoppedFourier.toLp_inner_eq_integral hf2 hf2] at hh
  have hn := congrArg (fun z : ℂ => RCLike.re z) hh
  simp only [inner_self_eq_norm_sq] at hn
  simpa only [SHE.StoppedFourier.toLp_norm_sq_eq_integral] using hn

/-- Exact Plancherel for the actual finite physical heat combination. -/
theorem heat_sum_energy_eq {q : ℕ} (t a : Fin q → ℝ) (z : Fin q → ℂ)
    (ht : ∀ i,0 < t i) :
    (∫ ξ : ℝ,‖frequencySum t a z ξ‖^2) = ∫ x : ℝ,‖physicalSum t a z x‖^2 := by
  have hF := fourier_physicalSum t a z ht
  have hF1 : Integrable (𝓕 (physicalSum t a z)) := by
    rw [hF]
    exact integrable_frequencySum t a z ht
  have hF2 : MemLp (𝓕 (physicalSum t a z)) 2 volume := by
    rw [hF]
    exact memLp_frequencySum t a z ht
  have hh := integral_norm_sq_fourier (integrable_physicalSum t a z ht) hF1
    (continuous_physicalSum t a z) (memLp_physicalSum t a z ht) hF2
  simpa only [hF] using hh

end SHE.FourierParseval
