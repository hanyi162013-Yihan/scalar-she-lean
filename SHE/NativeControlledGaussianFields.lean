module

public import SHE.DampedAffineGaussian
public import SHE.ObservationBlockMaps
public import SHE.NativePairExtendedMartingale
public import SHE.NativePairFutureMean

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.NativeControlledGaussianFields
open MeasureTheory Set GaussianIncrement NativeHeatObservation
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance nativeControlledGaussianFields_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeControlledGaussianFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {n : ℕ}

def initialDifference (u₀ v₀ : RealL2) (target : Fin n→ℝ) (centers : Fin n→HeatCircle) : State n :=
  WithLp.toLp 2 (fun i => functional (target i) (centers i) (v₀-u₀))

def terminalShift (Λ θ : ℝ) (u₀ v₀ : RealL2) (target : Fin n→ℝ) (centers : Fin n→HeatCircle) : State n :=
  WithLp.toLp 2 (fun i => θ*Real.exp (-Λ*target i)*functional (target i) (centers i) (v₀-u₀))

def mean (Λ θ : ℝ) (u₀ v₀ : RealL2) (target : Fin n→ℝ) (centers : Fin n→HeatCircle)
    (t : ℝ) (z : State (n+n)) : State n :=
  GaussianAffineFields.mean
    (DampedAffineGaussian.linear Λ θ (ObservationBlockMaps.first n) (ObservationBlockMaps.second n))
    (DampedAffineGaussian.shift Λ θ (initialDifference u₀ v₀ target centers)
      (terminalShift Λ θ u₀ v₀ target centers)) t z

theorem mean_apply {Λ θ t : ℝ} (ht : 0≤t) (u₀ v₀ : RealL2)
    (target : Fin n→ℝ) (centers : Fin n→HeatCircle) (z : State (n+n)) (i : Fin n) :
    mean Λ θ u₀ v₀ target centers t z i=
      z (Fin.castAdd n i)+θ*Real.exp (-Λ*t)*z (Fin.natAdd n i)+
        θ*Real.exp (-Λ*target i)*functional (target i) (centers i) (v₀-u₀)-
          θ*Real.exp (-Λ*t)*functional (target i) (centers i) (v₀-u₀) := by
  simp only [mean,GaussianAffineFields.mean,DampedAffineGaussian.linear,DampedAffineGaussian.shift,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,
    ObservationBlockMaps.first_apply,ObservationBlockMaps.second_apply,initialDifference,terminalShift,
    WithLp.ofLp_toLp,smul_eq_mul,ClippedExponential.coefficient,ClippedExponential.damping_eq ht]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)

/-- Exact samplewise controlled observation mean. The current-time
exponential is canceled against the actual extended martingale, while
the original-target exponential stays in its deterministic compensator. -/
theorem mean_extended_value (target : Fin n→ℝ) (centers : Fin n→HeatCircle) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<target i) (hqb : q≤b) (θ : ℝ) (ω : Ω) (i : Fin n) :
    mean Λ θ u₀ v₀ target centers (q:ℝ)
      (NativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S target centers b q ω) i=
      functional (target i-(q:ℝ)) (centers i) (S.first q ω)+
        θ*functional (target i-(q:ℝ)) (centers i) (S.second q ω-S.first q ω)+
        θ*Real.exp (-Λ*target i)*functional (target i) (centers i) (v₀-u₀)-
        θ*Real.exp (-Λ*(q:ℝ))*functional (target i) (centers i) (v₀-u₀) := by
  rw [mean_apply (show 0≤(q:ℝ) from q.2) u₀ v₀ target centers]
  simp only [NativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_left,Fin.append_right,
    NativePairLocalMartingale.value,min_eq_left hqb]
  have hage : target i-(b:ℝ)≤target i-(q:ℝ) := sub_le_sub_left (by exact_mod_cast hqb) _
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,← map_sub]
  dsimp only [Function.uncurry]
  have he : Real.exp (-Λ*(q:ℝ))*Real.exp (Λ*(q:ℝ))=1 := by
    rw [← Real.exp_add,show -Λ*(q:ℝ)+Λ*(q:ℝ)=0 by ring,Real.exp_zero]
  calc
    _=functional (target i-(q:ℝ)) (centers i) (S.first q ω)+
        θ*(Real.exp (-Λ*(q:ℝ))*Real.exp (Λ*(q:ℝ)))*
          functional (target i-(q:ℝ)) (centers i) (S.second q ω-S.first q ω)+
        θ*Real.exp (-Λ*target i)*functional (target i) (centers i) (v₀-u₀)-
        θ*Real.exp (-Λ*(q:ℝ))*functional (target i) (centers i) (v₀-u₀) := by ring
    _=_ := by rw [he]; ring

end SHE.NativeControlledGaussianFields
