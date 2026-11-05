module

public import SHEStochastic.MatrixDiffusionRows
public import SHEStochastic.StateDriverCovariance
public import SHEStochastic.MatrixInfiniteHaar

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixStateNoise
open MeasureTheory Filter MatrixInfiniteHaar StateNoiseCovariance
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
local instance matrixStateNoise_period : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance matrixStateNoise_twoFinite : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local notation "ν" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)

/-- The literal state-dependent noise row for one weighted component
observation, in physical spatial L2 coordinates. -/
def row (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) : Physical (d := d) :=
  StateNoiseCovariance.row ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k u

theorem row_ae (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) :
    row G hG hβ hβ1 i k u =ᵐ[ν] fun x => k x • MatrixDiffusionRows.row i (G.value (u x)) :=
  StateNoiseCovariance.row_ae ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k u

theorem row_continuous (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) :
    Continuous (row G hG hβ hβ1 i k) :=
  StateNoiseCovariance.row_continuous ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k

theorem row_bound (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) :
    ‖row G hG hβ hβ1 i k u‖ ≤ ‖k‖*(G.bound : ℝ) :=
  StateNoiseCovariance.row_bound ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k G.bound
    G.bound.coe_nonneg (MatrixDiffusionRows.coefficient_bound G i) u

/-- All component cross covariances are bounded continuous functions
of the vector state; off-diagonal entries are retained. -/
def covariance (i j : d) (k l : C(AddCircle (1 : ℝ),ℝ)) :
    BoundedContinuousFunction (Physical (d := d)) ℝ :=
  StateNoiseCovariance.bounded ν hβ hβ1 (MatrixDiffusionRows.holder hG i)
    (MatrixDiffusionRows.holder hG j) k l G.bound G.bound G.bound.coe_nonneg G.bound.coe_nonneg
    (MatrixDiffusionRows.coefficient_bound G i) (MatrixDiffusionRows.coefficient_bound G j)

theorem covariance_apply (i j : d) (k l : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) :
    covariance G hG hβ hβ1 i j k l u=
      inner ℝ (row G hG hβ hβ1 i k u) (row G hG hβ hβ1 j l u) := rfl

/-- These mixed state/driver brackets identify the noise carried by
the same joint weak limit. -/
def cross (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := d)) :
    BoundedContinuousFunction (Physical (d := d)) ℝ :=
  StateDriverCovariance.bounded ν hβ hβ1 (MatrixDiffusionRows.holder hG i) k b G.bound
    G.bound.coe_nonneg (MatrixDiffusionRows.coefficient_bound G i)

variable (K : MatrixNonlinearCoefficient.Coefficient d) {D : ℝ≥0} (hK : HolderWith D β K.value)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ z,‖G.value z-K.value z‖ ≤ δ)

include hδ hclose in
/-- Uniform square-diffusion approximation controls every actual row
uniformly over the entire infinite-dimensional state space. -/
theorem row_difference (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) :
    ‖row G hG hβ hβ1 i k u-row K hK hβ hβ1 i k u‖ ≤ ‖k‖*δ := by
  apply StateNoiseCovarianceStability.row_difference ν hβ hβ1
    (MatrixDiffusionRows.holder hG i) (MatrixDiffusionRows.holder hK i) k δ hδ _ u
  intro z
  rw [MatrixDiffusionRows.sub]
  exact (MatrixDiffusionRows.norm_le i _).trans (hclose z)

include hδ hclose in
theorem cross_difference (i : d) (k : C(AddCircle (1 : ℝ),ℝ))
    (b u : Physical (d := d)) :
    ‖cross G hG hβ hβ1 i k b u-cross K hK hβ hβ1 i k b u‖ ≤ ‖k‖*δ*‖b‖ := by
  apply StateDriverCovariance.difference ν hβ hβ1
    (MatrixDiffusionRows.holder hG i) (MatrixDiffusionRows.holder hK i) k b δ hδ _ u
  intro z
  rw [MatrixDiffusionRows.sub]
  exact (MatrixDiffusionRows.norm_le i _).trans (hclose z)

include hδ hclose in
theorem covariance_difference (i j : d) (k l : C(AddCircle (1 : ℝ),ℝ)) (u : Physical (d := d)) :
    ‖covariance G hG hβ hβ1 i j k l u-covariance K hK hβ hβ1 i j k l u‖ ≤
      ‖k‖*‖l‖*((G.bound : ℝ)+(K.bound : ℝ))*δ := by
  rw [covariance_apply,covariance_apply]
  have he : inner ℝ (row G hG hβ hβ1 i k u) (row G hG hβ hβ1 j l u)-
      inner ℝ (row K hK hβ hβ1 i k u) (row K hK hβ hβ1 j l u)=
      inner ℝ (row G hG hβ hβ1 i k u-row K hK hβ hβ1 i k u) (row G hG hβ hβ1 j l u)+
      inner ℝ (row K hK hβ hβ1 i k u) (row G hG hβ hβ1 j l u-row K hK hβ hβ1 j l u) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖row G hG hβ hβ1 i k u-row K hK hβ hβ1 i k u‖*‖row G hG hβ hβ1 j l u‖+
        ‖row K hK hβ hβ1 i k u‖*‖row G hG hβ hβ1 j l u-row K hK hβ hβ1 j l u‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ (‖k‖*δ)*(‖l‖*(G.bound : ℝ))+(‖k‖*(K.bound : ℝ))*(‖l‖*δ) :=
      add_le_add
        (mul_le_mul (row_difference G hG hβ hβ1 K hK δ hδ hclose i k u)
          (row_bound G hG hβ hβ1 j l u) (norm_nonneg _) (by positivity))
        (mul_le_mul (row_bound K hK hβ hβ1 i k u)
          (row_difference G hG hβ hβ1 K hK δ hδ hclose j l u) (norm_nonneg _) (by positivity))
    _ = _ := by ring

variable (Gn : ℕ → MatrixNonlinearCoefficient.Coefficient d) {Cn : ℕ → ℝ≥0}
    (hGn : ∀ r,HolderWith (Cn r) β (Gn r).value)

/-- Mixed state/driver covariances converge in the uniform function norm. -/
theorem uniform_cross_limit (error : ℕ → ℝ) (he : ∀ r,0 ≤ error r)
    (helim : Filter.Tendsto error Filter.atTop (𝓝 0))
    (happrox : ∀ r z,‖G.value z-(Gn r).value z‖ ≤ error r)
    (i : d) (k : C(AddCircle (1 : ℝ),ℝ)) (b : Physical (d := d)) :
    Filter.Tendsto (fun r => cross (Gn r) (hGn r) hβ hβ1 i k b)
      Filter.atTop (𝓝 (cross G hG hβ hβ1 i k b)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (r : ℕ) : ‖cross G hG hβ hβ1 i k b-cross (Gn r) (hGn r) hβ hβ1 i k b‖ ≤
      ‖k‖*error r*‖b‖ := by
    have her := he r
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro u
    exact cross_difference G hG hβ hβ1 (Gn r) (hGn r) (error r) (he r) (happrox r) i k b u
  have hh := squeeze_zero (fun r => norm_nonneg _) hb
    (by simpa only [mul_zero,zero_mul] using (tendsto_const_nhds.mul helim).mul_const ‖b‖)
  simpa only [norm_sub_rev] using hh

/-- Every off-diagonal state covariance also converges uniformly. -/
theorem uniform_covariance_limit (B : ℝ) (hB : ∀ r,((Gn r).bound : ℝ) ≤ B)
    (error : ℕ → ℝ) (he : ∀ r,0 ≤ error r)
    (helim : Filter.Tendsto error Filter.atTop (𝓝 0))
    (happrox : ∀ r z,‖G.value z-(Gn r).value z‖ ≤ error r)
    (i j : d) (k l : C(AddCircle (1 : ℝ),ℝ)) :
    Filter.Tendsto (fun r => covariance (Gn r) (hGn r) hβ hβ1 i j k l)
      Filter.atTop (𝓝 (covariance G hG hβ hβ1 i j k l)) := by
  have hB0 : 0 ≤ B := ((Gn 0).bound.coe_nonneg).trans (hB 0)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb (r : ℕ) : ‖covariance G hG hβ hβ1 i j k l-
      covariance (Gn r) (hGn r) hβ hβ1 i j k l‖ ≤ ‖k‖*‖l‖*((G.bound : ℝ)+B)*error r := by
    have her := he r
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro u
    exact (covariance_difference G hG hβ hβ1 (Gn r) (hGn r) (error r) (he r) (happrox r) i j k l u).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add (le_refl (G.bound : ℝ)) (hB r))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (he r))
  have hh := squeeze_zero (fun r => norm_nonneg _) hb
    (by simpa only [mul_zero] using tendsto_const_nhds.mul helim)
  simpa only [norm_sub_rev] using hh

end SHEStochastic.MatrixStateNoise
