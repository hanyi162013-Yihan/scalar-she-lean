module

public import SHE.NativeControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.InterpolatedPredictableRows
open MeasureTheory PredictableL2 OrthogonalItoChannels PredictableItoRotation
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
local instance interpolatedPredictableRows_blockSigma : MeasurableSpace (Both C) := borel _
local instance interpolatedPredictableRows_blockBorel : BorelSpace (Both C) := ⟨rfl⟩
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

def rescaledDifference {Λ : ℝ} (hΛ : 0≤Λ) (b : ℝ≥0)
    (u v : Process (E := C) 𝓕 μ H) : Process (E := Both C) 𝓕 μ H :=
  processIsometry 𝓕 μ H (fun _ => right (C := C)) (right_measurable 𝓕)
    (Real.exp (Λ*(b:ℝ)) • PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
      (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) (v-u))

/-- The integrating factor disappears from the actual instantaneous
interpolated noise. The additive row is unchanged, and the common-Haar
residual rows interpolate with the literal coefficients 1-theta, theta. -/
theorem interpolated_ae {Λ : ℝ} (hΛ : 0≤Λ) (b : ℝ≥0) (θ : ℝ)
    (v₀ u v : Process (E := C) 𝓕 μ H) :
    ∀ᵐ p ∂energyMeasure μ H,p.1≤b →
      TwoChannelItoRows.block 𝓕 μ H v₀ u p+ClippedExponential.coefficient Λ θ (p.1:ℝ) •
        rescaledDifference 𝓕 μ H hΛ b u v p=
      WithLp.toLp 2 (v₀ p,(1-θ) • u p+θ • v p) := by
  let w := PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ b)
    (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) (v-u)
  have hr := processIsometry_ae 𝓕 μ H (fun _ => right (C := C)) (right_measurable 𝓕)
    (Real.exp (Λ*(b:ℝ)) • w)
  have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_smul (Real.exp (Λ*(b:ℝ))) w)
  have hd := ae_eq_of_ae_eq_trim (Lp.coeFn_sub v u)
  filter_upwards [TwoChannelItoRows.block_ae 𝓕 μ H v₀ u,hr,hs,
    PredictableContraction.weighted_ae 𝓕 μ H (PredictableDamping.weight Λ b)
      (PredictableDamping.weight_predictable 𝓕 Λ b) (PredictableDamping.weight_bound hΛ b) (v-u),hd]
    with p hb hr hs hw hd hp
  change w p=PredictableDamping.weight Λ b p • (v-u) p at hw
  change rescaledDifference 𝓕 μ H hΛ b u v p=right ((Real.exp (Λ*(b:ℝ)) • w) p) at hr
  change (Real.exp (Λ*(b:ℝ)) • w) p=Real.exp (Λ*(b:ℝ)) • w p at hs
  change (v-u) p=v p-u p at hd
  rw [hb,hr,hs,hw,hd]
  have hpb : (p.1:ℝ)≤(b:ℝ) := by exact_mod_cast hp
  have he : ClippedExponential.coefficient Λ θ (p.1:ℝ)*Real.exp (Λ*(b:ℝ))*
      PredictableDamping.weight Λ b p=θ := by
    rw [ClippedExponential.coefficient,ClippedExponential.damping_eq (show 0≤(p.1:ℝ) from p.1.2),
      PredictableDamping.weight_eq hpb]
    have hexp : Real.exp (-Λ*(p.1:ℝ))*Real.exp (Λ*(b:ℝ))*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))=1 := by
      rw [← Real.exp_add,← Real.exp_add,show -Λ*(p.1:ℝ)+Λ*(b:ℝ)+ -Λ*((b:ℝ)-(p.1:ℝ))=0 by ring,Real.exp_zero]
    calc
      _=θ*(Real.exp (-Λ*(p.1:ℝ))*Real.exp (Λ*(b:ℝ))*Real.exp (-Λ*((b:ℝ)-(p.1:ℝ)))) := by ring
      _=_ := by rw [hexp,mul_one]
  calc
    _=WithLp.toLp 2 (v₀ p,u p)+right (θ • (v p-u p)) := by
      rw [← map_smul,smul_smul,smul_smul,he]
    _=_ := by
      apply WithLp.ofLp_injective
      change (v₀ p,u p)+(0,θ • (v p-u p))=(v₀ p,(1-θ) • u p+θ • v p)
      ext
      · simp
      · change u p+θ • (v p-u p)=(1-θ) • u p+θ • v p
        module

end SHE.InterpolatedPredictableRows
