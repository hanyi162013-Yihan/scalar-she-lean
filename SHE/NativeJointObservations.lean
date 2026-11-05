module

public import SHE.FiniteItoBlockMap
public import SHE.NativePairExtendedMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeJointObservations
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open scoped NNReal ENNReal
local instance nativeJointObservations_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointObservations_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointObservations_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointObservations_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointObservations_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointObservations_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {n : ℕ}

def weights (Λ : ℝ) (Z : Fin n→WordRecursion.Observation) : Fin n→ℝ :=
  fun i => Real.exp (-Λ*(Z i).stop)

def initial (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation) : State n :=
  FiniteItoBlockMap.blockMap (weights Λ Z)
    (NativePairExtendedMartingale.initial u₀ v₀ (fun i => (Z i).target) (fun i => (Z i).center))

@[simp] theorem initial_apply (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation) (i : Fin n) :
    initial Λ u₀ v₀ Z i=functional (Z i).target (Z i).center u₀+
      Real.exp (-Λ*(Z i).stop)*functional (Z i).target (Z i).center (v₀-u₀) := by
  simp only [initial,FiniteItoBlockMap.blockMap_apply,NativePairExtendedMartingale.initial,
    WithLp.ofLp_toLp,Fin.append_left,Fin.append_right,weights]

theorem initial_physical_mean (Λ : ℝ) (u₀ v₀ : RealL2) (Z : Fin n→WordRecursion.Observation)
    (hT : ∀ i,0<(Z i).target) (i : Fin n) :
    initial Λ u₀ v₀ Z i=PhysicalProfile.physicalHeatMean (embed u₀) ((Z i).target,(Z i).center)+
      Real.exp (-Λ*(Z i).stop)*PhysicalProfile.physicalHeatMean (embed (v₀-u₀)) ((Z i).target,(Z i).center) := by
  rw [initial_apply,functional_physical (hT i),functional_physical (hT i)]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (Z : Fin n→WordRecursion.Observation) (b : ℝ≥0)
variable (hgap : ∀ i,(b:ℝ)<(Z i).target)

/-- The printed drift-cancelling joint observations are a constant
linear image of the genuine extended observation martingale. Each
original stop remains separate from its heat target. -/
def value (t : ℝ≥0) (ω : Ω) : State n :=
  FiniteItoBlockMap.blockMap (weights Λ Z)
    (NativePairExtendedMartingale.value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b t ω)

def rows (hΛ : 0≤Λ) : Fin n→Process (E := Both RealHaarInput) 𝓕 μ H :=
  FiniteItoBlockMap.rows 𝓕 μ H (weights Λ Z)
    (NativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ)

theorem continuous_value (ω : Ω) :
    Continuous (fun t => value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b t ω) :=
  (FiniteItoBlockMap.blockMap (weights Λ Z)).continuous.comp
    (NativePairExtendedMartingale.continuous_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b ω)

include hgap in
theorem value_eq_physical (q : ℝ≥0) (hqb : q≤b) (ω : Ω) (i : Fin n) :
    value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω i=
      functional ((Z i).target-(q:ℝ)) (Z i).center (S.first q ω)+
        Real.exp (-Λ*((Z i).stop-(q:ℝ)))*
          functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω-S.first q ω) := by
  rw [value,FiniteItoBlockMap.blockMap_apply]
  simp only [NativePairExtendedMartingale.value,WithLp.ofLp_toLp,Fin.append_left,Fin.append_right,
    NativePairLocalMartingale.value,min_eq_left hqb,weights]
  have hage : (Z i).target-(b:ℝ)≤(Z i).target-(q:ℝ) := sub_le_sub_left (by exact_mod_cast hqb) _
  rw [PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,
    PositiveGapObservations.coordinate_eq_functional (sub_pos.mpr (hgap i)) _ _ _ hage,← map_sub]
  dsimp only [Function.uncurry]
  have he : Real.exp (-Λ*(Z i).stop)*Real.exp (Λ*(q:ℝ))=Real.exp (-Λ*((Z i).stop-(q:ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc,he]

include hgap in
theorem value_at_original_stop (q : ℝ≥0) (hqb : q≤b) (ω : Ω) (i : Fin n) (hstop : (Z i).stop=(q:ℝ)) :
    value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b q ω i=
      functional ((Z i).target-(q:ℝ)) (Z i).center (S.second q ω) := by
  rw [value_eq_physical 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap q hqb ω i,hstop,
    sub_self,mul_zero,Real.exp_zero,one_mul,map_sub]
  ring

include hIJ₀ hIJ₁ in
theorem integral_representation (hΛ : 0≤Λ) (hbH : b≤H) (t : ℝ≥0) :
    value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b t=ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J (initial Λ u₀ v₀ Z)
        (rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b hgap hΛ) t := by
  have he := NativePairExtendedMartingale.integral_representation 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
    J hIJ₀ hIJ₁ (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ hbH t
  have hm := FiniteItoBlockMap.vectorIntegral_map 𝓕 μ H J (weights Λ Z)
    (NativePairExtendedMartingale.initial u₀ v₀ (fun i => (Z i).target) (fun i => (Z i).center))
    (NativePairExtendedMartingale.rows 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hΛ) t
  filter_upwards [he,hm] with ω he hm
  change FiniteItoBlockMap.blockMap (weights Λ Z) _=_
  rw [he]
  exact hm

include hIJ₀ hIJ₁ hgap in
theorem predictable_value (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hΛ : 0≤Λ) (hbH : b≤H) :
    StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z b)) :=
  (FiniteItoBlockMap.blockMap (weights Λ Z)).continuous.comp_stronglyMeasurable
    (NativePairExtendedMartingale.predictable_value 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
      (fun i => (Z i).target) (fun i => (Z i).center) b hgap hnull hΛ hbH)

end SHE.NativeJointObservations
