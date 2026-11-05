module

public import SHEStochastic.FiniteSynthesisBessel
public import SHEStochastic.RieszFiniteExtension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.WeightedRieszSynthesis
open Finset
open scoped ENNReal NNReal

variable {ι E : Type*} [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A weighted Kronecker Gram identity gives the exact energy of every
finite linear combination. -/
theorem finite_energy (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (s : Finset ι) (z : ι → ℝ) :
    inner ℝ (∑ i∈s, z i • a i) (M (∑ i∈s, z i • a i))=∑ i∈s, ‖z i‖^2 := by
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, hGram]
  simp [Real.norm_eq_abs, sq_abs, pow_two]

theorem finite_upper (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u))
    (s : Finset ι) (z : ι → ℝ) :
    ‖∑ i∈s, z i • a i‖^2 ≤ m⁻¹*(∑ i∈s, ‖z i‖^2) := by
  have hh := hLo (∑ i∈s, z i • a i)
  rw [finite_energy a M hGram] at hh
  exact (le_inv_mul_iff₀ hm).mpr hh

theorem finite_lower (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (U : ℝ) (hU : 0 < U) (hHi : ∀ u, inner ℝ u (M u) ≤ U*‖u‖^2)
    (s : Finset ι) (z : ι → ℝ) :
    U⁻¹*(∑ i∈s, ‖z i‖^2) ≤ ‖∑ i∈s, z i • a i‖^2 := by
  have hh := hHi (∑ i∈s, z i • a i)
  rw [finite_energy a M hGram] at hh
  exact (inv_mul_le_iff₀ hU).mpr hh

/-- Reuse the common Bessel construction for an actual infinite
weighted-Haar synthesis operator. -/
def synthesis [CompleteSpace E] (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u)) :
    lp (fun _ : ι => ℝ) 2 →L[ℝ] E :=
  FiniteSynthesisBessel.synthesis a m⁻¹ (inv_nonneg.mpr hm.le) (finite_upper a M hGram m hm hLo)

theorem synthesis_single [CompleteSpace E] (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u)) (i : ι) :
    synthesis a M hGram m hm hLo (lp.single 2 i 1)=a i :=
  FiniteSynthesisBessel.synthesis_single a m⁻¹ (inv_nonneg.mpr hm.le)
    (finite_upper a M hGram m hm hLo) i

theorem lower [CompleteSpace E] (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u))
    (U : ℝ) (hU : 0 < U) (hHi : ∀ u, inner ℝ u (M u) ≤ U*‖u‖^2)
    (x : lp (fun _ : ι => ℝ) 2) :
    U⁻¹*‖x‖^2 ≤ ‖synthesis a M hGram m hm hLo x‖^2 :=
  RieszFiniteExtension.lower _ a (synthesis_single a M hGram m hm hLo) U⁻¹
    (finite_lower a M hGram U hU hHi) x

/-- The standard `ℓ²` finite-support density reduces bounded-operator
identities to their values on the canonical single vectors. -/
theorem ext_single (S T : lp (fun _ : ι => ℝ) 2 →L[ℝ] E)
    (h : ∀ i, S (lp.single 2 i 1)=T (lp.single 2 i 1)) : S=T := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal)≠⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro r
  change S (lp.single 2 i r)=T (lp.single 2 i r)
  have he : lp.single (E := fun _ : ι => ℝ) 2 i r=r • lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ) := by
    simpa only [smul_eq_mul, mul_one] using lp.single_smul (E := fun _ : ι => ℝ) 2 i r (1 : ℝ)
  rw [he, map_smul, map_smul, h]

/-- The infinite weighted Gram identity is an actual operator identity,
obtained from the countable column Gram theorem. -/
theorem weighted_identity [CompleteSpace E] (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u)) :
    let S := synthesis a M hGram m hm hLo
    S.adjoint.comp (M.comp S)=ContinuousLinearMap.id ℝ (lp (fun _ : ι => ℝ) 2) := by
  dsimp only
  apply ext_single
  intro j
  simp only [ContinuousLinearMap.comp_apply, synthesis_single, ContinuousLinearMap.id_apply]
  apply lp.ext
  funext i
  have hh := ContinuousLinearMap.adjoint_inner_right (synthesis a M hGram m hm hLo)
    (lp.single 2 i 1) (M (a j))
  rw [synthesis_single, hGram, lp.inner_single_left] at hh
  simpa [lp.single_apply, Pi.single_apply, eq_comm] using hh

/-- Completeness of the columns and the Riesz bounds make the actual
infinite synthesis bijective; no abstract basis property is assumed. -/
theorem bijective [CompleteSpace E] (a : ι → E) (M : E →L[ℝ] E)
    (hGram : ∀ i j, inner ℝ (a i) (M (a j))=if i=j then 1 else 0)
    (m : ℝ) (hm : 0 < m) (hLo : ∀ u, m*‖u‖^2 ≤ inner ℝ u (M u))
    (U : ℝ) (hU : 0 < U) (hHi : ∀ u, inner ℝ u (M u) ≤ U*‖u‖^2)
    (hDense : (Submodule.span ℝ (Set.range a)).topologicalClosure=⊤) :
    Function.Bijective (synthesis a M hGram m hm hLo) := by
  let S := synthesis a M hGram m hm hLo
  have hspan : Submodule.span ℝ (Set.range a) ≤ S.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨lp.single 2 i 1, synthesis_single a M hGram m hm hLo i⟩
  have hRange : S.range.topologicalClosure=⊤ := by
    apply top_unique
    rw [← hDense]
    exact Submodule.topologicalClosure_mono hspan
  have hbelow (x : lp (fun _ : ι => ℝ) 2) : ‖x‖ ≤ Real.sqrt U*‖S x‖ := by
    have hh := (inv_mul_le_iff₀ hU).mp (lower a M hGram m hm hLo U hU hHi x)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg U) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hU.le]
    exact hh
  exact (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz S).mpr
    ⟨hRange, ⟨⟨Real.sqrt U, Real.sqrt_nonneg U⟩, S.antilipschitz_of_bound hbelow⟩⟩

end SHEStochastic.WeightedRieszSynthesis
