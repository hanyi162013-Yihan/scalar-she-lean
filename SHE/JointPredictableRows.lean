module

public import SHE.InterpolatedPredictableRows

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.JointPredictableRows
open MeasureTheory PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
local instance jointPredictableRows_blockSigma : MeasurableSpace (Both C) := borel _
local instance jointPredictableRows_blockBorel : BorelSpace (Both C) := ⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

/-- Exact noise row of a drift-cancelling joint coordinate with arbitrary
original stop sigma. The fixed coefficient exp(-Lambda sigma) is kept
distinct from the physical target and the current time. -/
theorem joint_ae {Λ : ℝ} (hΛ : 0≤Λ) (b : ℝ≥0) (σ : ℝ)
    (v₀ u v : Process (E := C) 𝓕 μ H) :
    ∀ᵐ p ∂energyMeasure μ H,p.1≤b →
      TwoChannelItoRows.block 𝓕 μ H v₀ u p+Real.exp (-Λ*σ) •
        InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b u v p=
      WithLp.toLp 2 (v₀ p,v p+(1-Real.exp (-Λ*(σ-(p.1:ℝ)))) • (u p-v p)) := by
  filter_upwards [InterpolatedPredictableRows.interpolated_ae 𝓕 μ H hΛ b 1 v₀ u v,
    TwoChannelItoRows.block_ae 𝓕 μ H v₀ u] with p h1 h0 hp
  have hh := h1 hp
  rw [ClippedExponential.coefficient,one_mul,
    ClippedExponential.damping_eq (show 0≤(p.1:ℝ) from p.1.2)] at hh
  simp only [sub_self,zero_smul,one_smul,zero_add] at hh
  let A := TwoChannelItoRows.block 𝓕 μ H v₀ u p
  let B := InterpolatedPredictableRows.rescaledDifference 𝓕 μ H hΛ b u v p
  have hd : Real.exp (-Λ*(p.1:ℝ)) • B=WithLp.toLp 2 (v₀ p,v p)-A :=
    (eq_sub_iff_add_eq).mpr (by rw [add_comm];exact hh)
  have he : Real.exp (-Λ*(σ-(p.1:ℝ)))*Real.exp (-Λ*(p.1:ℝ))=Real.exp (-Λ*σ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change A+Real.exp (-Λ*σ) • B=_
  calc
    _=A+Real.exp (-Λ*(σ-(p.1:ℝ))) • (Real.exp (-Λ*(p.1:ℝ)) • B) := by rw [smul_smul,he]
    _=A+Real.exp (-Λ*(σ-(p.1:ℝ))) • (WithLp.toLp 2 (v₀ p,v p)-A) := by rw [hd]
    _=WithLp.toLp 2 (v₀ p,u p)+Real.exp (-Λ*(σ-(p.1:ℝ))) •
        (WithLp.toLp 2 (v₀ p,v p)-WithLp.toLp 2 (v₀ p,u p)) := by dsimp only [A];rw [h0]
    _=_ := by
      apply WithLp.ofLp_injective
      change (v₀ p,u p)+Real.exp (-Λ*(σ-(p.1:ℝ))) • ((v₀ p,v p)-(v₀ p,u p))=
        (v₀ p,v p+(1-Real.exp (-Λ*(σ-(p.1:ℝ)))) • (u p-v p))
      ext
      · simp
      · change u p+Real.exp (-Λ*(σ-(p.1:ℝ))) • (v p-u p)=
          v p+(1-Real.exp (-Λ*(σ-(p.1:ℝ)))) • (u p-v p)
        module

end SHE.JointPredictableRows
