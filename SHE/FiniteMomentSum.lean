module

public import SHE.GaussianClipProducts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteMomentSum
open Set MeasureTheory Real
open scoped BigOperators

theorem sum_pow_le {ι : Type*} [Fintype ι] (q : ℕ) (hq : 0 < q)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i,a i)^q ≤ (Fintype.card ι : ℝ)^(q-1)*∑ i,(a i)^q := by
  have hp : 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have hh := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := Finset.univ) (f := a) hp (fun i _ => ha i)
  have he : (q : ℝ)-1 = ((q-1 : ℕ) : ℝ) := by rw [Nat.cast_sub (by omega)]; norm_num
  simpa only [he,Real.rpow_natCast,Finset.card_univ] using hh

/-- Finite sums of correlated terms keep a common moment scale. The
constant depends on their finite count, with no independence assumption. -/
theorem dominated_power_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (q : ℕ) (hq : 0 < q) (f : ι → Ω → ℝ)
    (hf : ∀ i, Measurable (f i)) (hn : ∀ i x, 0 ≤ f i x)
    (hi : ∀ i, Integrable (fun x => f i x^q) μ)
    {B C S : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hb : ∀ i, (∫ x,f i x^q ∂μ) ≤ C*S^q)
    (R : Ω → ℝ) (hR : Measurable R)
    (hdom : ∀ x, |R x| ≤ B*∑ i,f i x) :
    Integrable (fun x => |R x|^q) μ ∧
      (∫ x,|R x|^q ∂μ) ≤ C*(B*(Fintype.card ι : ℝ)*S)^q := by
  let N : ℝ := Fintype.card ι
  let bound := fun x => B^q*N^(q-1)*∑ i,f i x^q
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hib : Integrable bound μ :=
    (integrable_finsetSum _ (fun i _ => hi i)).const_mul _
  have hpoint (x : Ω) : |R x|^q ≤ bound x := by
    calc
      _ ≤ (B*∑ i,f i x)^q := pow_le_pow_left₀ (abs_nonneg _) (hdom x) q
      _ = B^q*(∑ i,f i x)^q := mul_pow _ _ _
      _ ≤ B^q*(N^(q-1)*∑ i,f i x^q) :=
        mul_le_mul_of_nonneg_left (sum_pow_le q hq (fun i => f i x) (fun i => hn i x))
          (pow_nonneg hB _)
      _ = bound x := by dsimp [bound]; ring
  have hiR : Integrable (fun x => |R x|^q) μ :=
    hib.mono' (by fun_prop) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpoint x))
  refine ⟨hiR,?_⟩
  calc
    _ ≤ ∫ x,bound x ∂μ := integral_mono hiR hib hpoint
    _ = B^q*N^(q-1)*∑ i,∫ x,f i x^q ∂μ := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ B^q*N^(q-1)*∑ _ : ι,C*S^q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i))
        (mul_nonneg (pow_nonneg hB _) (pow_nonneg hN _))
    _ = C*(B*(Fintype.card ι : ℝ)*S)^q := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hp : N^(q-1)*N = N^q := by rw [← pow_succ,Nat.sub_add_cancel (by omega)]
      change B^q*N^(q-1)*(N*(C*S^q)) = C*(B*N*S)^q
      rw [mul_pow,mul_pow]
      calc
        _ = C*B^q*(N^(q-1)*N)*S^q := by ring
        _ = _ := by rw [hp]; ring

end SHE.FiniteMomentSum
