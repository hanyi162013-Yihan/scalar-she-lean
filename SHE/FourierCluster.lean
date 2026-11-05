module

public import SHE.HeatLine

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.FourierCluster
open MeasureTheory SHE.HeatAnnihilator SHE.HeatSpanCluster SHE.HeatLine

/-- The frequency-side Gaussian in the standard Fourier convention
`exp (-2*pi*I*x*xi)`. The physical heat kernel has this multiplier. -/
def frequencyParameter (t a : ℝ) : Parameter :=
  (((4*Real.pi^2*t:ℝ):ℂ),((-2*Real.pi*a:ℝ):ℂ)*Complex.I)

def frequencyGaussian (t a : ℝ) : ℂ → ℂ := gaussian (frequencyParameter t a)

def phase (c : ℝ) (z : ℂ) : ℂ := Complex.exp (((2*Real.pi*c:ℝ):ℂ)*Complex.I*z)

theorem frequencyGaussian_phase (t a c : ℝ) (z : ℂ) :
    phase c z*frequencyGaussian t a z = frequencyGaussian t (a-c) z := by
  unfold phase frequencyGaussian gaussian frequencyParameter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_norm (c x : ℝ) : ‖phase c (x:ℂ)‖=1 := by
  unfold phase
  rw [Complex.norm_exp]
  simp

theorem phase_span {q : ℕ} (t a : Fin q → ℝ) (c : ℝ) (f : ℂ → ℂ)
    (hf : f ∈ Submodule.span ℂ (Set.range (fun i => frequencyGaussian (t i) (a i)))) :
    (fun z => phase c z*f z) ∈ Submodule.span ℂ
      (Set.range (fun i => frequencyGaussian (t i) (a i-c))) := by
  obtain ⟨d,hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
  refine ⟨d,?_⟩
  funext z
  have he := congrFun hd z
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he ⊢
  rw [← he,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← frequencyGaussian_phase]
  ring

def normalizedParameter (t a T : ℝ) : Parameter :=
  (((4*Real.pi^2*t/T:ℝ):ℂ),((-2*Real.pi*a/Real.sqrt T:ℝ):ℂ)*Complex.I)

theorem normalizedParameter_eq (t a : ℝ) {T : ℝ} (hT : 0 < T) :
    affineParameter (frequencyParameter t a) 0 ((Real.sqrt T)⁻¹:ℂ) = normalizedParameter t a T := by
  have hs := Real.sqrt_pos.mpr hT
  have hsq : (Real.sqrt T)^2=T := Real.sq_sqrt hT.le
  have hsqC : ((Real.sqrt T:ℂ))^2=(T:ℂ) := by exact_mod_cast hsq
  have hTC : (T:ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hSC : (Real.sqrt T:ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  apply Prod.ext
  · dsimp [affineParameter,frequencyParameter,normalizedParameter]
    push_cast
    field_simp
    rw [hsqC]
  · dsimp [affineParameter,frequencyParameter,normalizedParameter]
    push_cast
    simp only [mul_zero,sub_zero]
    field_simp

theorem normalizedParameter_bounds {t a T δ B : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (_hB : 0 ≤ B) (ht : δ*T ≤ t) (htT : t ≤ T) (ha : |a| ≤ B*Real.sqrt T) :
    ‖normalizedParameter t a T‖ ≤ max (4*Real.pi^2) (2*Real.pi*B) ∧
      4*Real.pi^2*δ ≤ (normalizedParameter t a T).1.re ∧
      (normalizedParameter t a T).2.re = 0 := by
  have ht0 : 0 < t := (mul_pos hδ hT).trans_le ht
  have hs := Real.sqrt_pos.mpr hT
  have hP : 0 < 4*Real.pi^2 := by positivity
  have hreal : 0 ≤ 4*Real.pi^2*t/T := by positivity
  have hupper : 4*Real.pi^2*t/T ≤ 4*Real.pi^2 :=
    (div_le_iff₀ hT).mpr (mul_le_mul_of_nonneg_left htT hP.le)
  have hlower : 4*Real.pi^2*δ ≤ 4*Real.pi^2*t/T := by
    apply (le_div_iff₀ hT).mpr
    nlinarith [mul_le_mul_of_nonneg_left ht hP.le]
  have hb : |(-2*Real.pi*a/Real.sqrt T)| ≤ 2*Real.pi*B := by
    rw [abs_div,abs_mul,abs_mul,abs_neg,abs_two,abs_of_pos Real.pi_pos,abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ 2*Real.pi by positivity)]
  refine ⟨?_,?_,?_⟩
  · rw [Prod.norm_def,max_le_iff]
    constructor
    · apply le_trans (b := 4*Real.pi^2)
      · simpa [normalizedParameter,← Complex.ofReal_pow,Complex.norm_real,abs_of_nonneg hreal,abs_of_pos ht0,abs_of_pos hT] using hupper
      · exact le_max_left _ _
    · apply le_trans (b := 2*Real.pi*B)
      · simpa [normalizedParameter,norm_mul,abs_div,abs_mul,abs_neg,abs_of_pos hs,abs_of_pos Real.pi_pos] using hb
      · exact le_max_right _ _
  · simpa [normalizedParameter,← Complex.ofReal_pow] using hlower
  · simp [normalizedParameter]

/-- A compact physical heat cluster has a genuine Fourier-side Gaussian
envelope. The phase shift removes the common physical center without
altering its actual line L² energy. -/
theorem compact_fourier_cluster_envelope (q : ℕ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ C : ℝ,0 < C ∧ ∀ (t a : Fin q → ℝ) (T c : ℝ),0 < T →
      (∀ i,δ*T ≤ t i) → (∀ i,t i ≤ T) → (∀ i,|a i-c| ≤ B*Real.sqrt T) →
      ∀ f : ℂ → ℂ,f ∈ Submodule.span ℂ
        (Set.range (fun i => frequencyGaussian (t i) (a i))) →
      Integrable (fun ξ : ℝ => ‖f (ξ:ℂ)‖^2) ∧ ∀ ξ : ℝ,
        ‖f (ξ:ℂ)‖^2 ≤ C*Real.sqrt T*(∫ u : ℝ,‖f (u:ℂ)‖^2)*
          Real.exp (-(4*Real.pi^2*δ)*T*ξ^2) := by
  have hγ : 0 < 2*Real.pi^2*δ := by positivity
  obtain ⟨C,hC,hb⟩ := affine_gaussian_span_global_envelope q
    (max (4*Real.pi^2) (2*Real.pi*B)) (γ:=2*Real.pi^2*δ) (k:=2*Real.pi^2*δ)
    (B:=0) hγ hγ
  refine ⟨C,hC,fun t a T c hT ht htT ha f hf => ?_⟩
  let g : ℂ → ℂ := fun z => phase c z*f z
  have hg : g ∈ Submodule.span ℂ (Set.range (fun i => gaussian (frequencyParameter (t i) (a i-c)))) :=
    phase_span t a c f hf
  have hs := Real.sqrt_pos.mpr hT
  have hnorm (x : ℝ) : ‖g (x:ℂ)‖ = ‖f (x:ℂ)‖ := by
    simp only [g,norm_mul,phase_norm,one_mul]
  have hp (i : Fin q) := normalizedParameter_bounds hT hδ hB (ht i) (htT i) (ha i)
  obtain ⟨hi,hb⟩ := hb (fun i => frequencyParameter (t i) (a i-c)) 0 (Real.sqrt T)⁻¹
    (inv_pos.mpr hs) (by
      apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (by positivity))).mpr
      intro i
      simp only [Complex.ofReal_zero,Complex.ofReal_inv]
      rw [normalizedParameter_eq _ _ hT]
      exact (hp i).1)
    (by intro i; simp only [Complex.ofReal_zero,Complex.ofReal_inv]; rw [normalizedParameter_eq _ _ hT]; nlinarith [(hp i).2.1])
    (by intro i; simp only [Complex.ofReal_zero,Complex.ofReal_inv]; rw [normalizedParameter_eq _ _ hT,(hp i).2.2]; simp)
    g hg
  simp_rw [hnorm] at hi hb
  refine ⟨hi,fun ξ => ?_⟩
  have he : -(2*(2*Real.pi^2*δ))*((ξ-0)/(Real.sqrt T)⁻¹)^2 =
      -(4*Real.pi^2*δ)*T*ξ^2 := by
    rw [sub_zero,div_inv_eq_mul,mul_pow,Real.sq_sqrt hT.le]
    ring
  simpa only [inv_inv,he] using hb ξ

end SHE.FourierCluster
